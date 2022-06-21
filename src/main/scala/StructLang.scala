import java.util.HexFormat
import java.lang
import scala.util.Try
import fastparse.internal.Instrument
import java.io.FileReader
import java.io.FileInputStream

/*
Language overview

Define elements:

weirdStruct := {
    u2 major;
    assert (major == 1); // stop parsing on unexpected data
    u2; // name optional
    // automatic align unless overridden with @pack or @align(n)
    otherType*[4] arr; // arrays and pointers (complex types always innermost left to outermost right)
    // this means indexing arr[5][10] requires the array is (at least) type[11][6]
    @pack { u2; u1; } inlineStruct;
    repeat u1 until (_ == 0); // array of unspecified size, parens mandatory
    repeat {
        u1 tag;
        if (tag != 0) varint len;
        if (tag != 0) u1[len.val] raw;
        if (tag != 0) match { // u1 buffers can be reused as things to reparse -- NOTE: does this make pointers relative to the new buffer?
            (tag == 1): in(raw) repeat u1 eof;
            (tag == 2): in(raw) repeat varint eof;
            (tag == 3): in(raw) randomComplexType;
            // fallthrough automatically fails to parse
        } parsed;
    } until (_.tag == 0) selfTerminatedTlvArray;
    repeat repeat u1 until (_ == 0) until (_.length == 1) stringTable;
    // TODO: at(<object base>[+offset]) type;
    // maybe at(addr) and provide .base on objects (how does this interact with in(..)?)
};

varint := @pack {
    repeat u1 until (_ & 0x80 == 0) raw;
    assert (raw.length);
    calc (
        u8 val = 0;
        for (e <- raw) val = (val << 7) | e & 0x7f;
        val
    ) value;
};
*/

object Ast {
    case class Ident(name: String)
    sealed trait Top
    object Top {
        case class TypeDef(name: Ident, ty: Type) extends Top
    }
    sealed trait Type
    object Type {
        case class Annotated(annot: Annotation, ty: Type) extends Type
        case class Named(name: Ident) extends Type
        case class Struct(body: Seq[Stmt]) extends Type
        case class Pointer(to: Type) extends Type
        case class Array(of: Type, len: Expr) extends Type
        case class Repeated(what: Type, cond: RepeatCond) extends Type
        case class Conditional(cond: Expr, ty: Type) extends Type
        case class Inside(buf: Expr, ty: Type) extends Type
        case class Match(arms: Seq[MatchArm]) extends Type
        case class Assert(pred: Expr) extends Type
        case class Calc(expr: Expr) extends Type
    }
    sealed trait Annotation
    object Annotation {
        case class Align(alignment: Int) extends Annotation
        case object Pack extends Annotation
    }
    sealed trait RepeatCond
    object RepeatCond {
        case object Eof extends RepeatCond
        case class Until(pred: Expr) extends RepeatCond
        case class While(pred: Expr) extends RepeatCond
    }
    sealed trait Expr
    object Expr {
        case class ConstantNum(value: Long) extends Expr
        case class ConstantBytes(value: IndexedSeq[Byte]) extends Expr
        case class Variable(name: Ident) extends Expr
        case class Ternary(cond: Expr, left: Expr, right: Expr) extends Expr
        case class Binary(left: Expr, op: BinOp, right: Expr) extends Expr
        case class Unary(op: UnOp, of: Expr) extends Expr
        case class Prop(obj: Expr, name: Ident) extends Expr
        case class Index(arr: Expr, idx: Expr) extends Expr
    }
    sealed trait BinOp
    object BinOp {
        case object Mul extends BinOp
        case object Div extends BinOp
        case object Mod extends BinOp
        case object Add extends BinOp
        case object Sub extends BinOp
        case object And extends BinOp
        case object Xor extends BinOp
        case object Or extends BinOp
        case object Shl extends BinOp
        case object Shr extends BinOp

        case object Eq extends BinOp
        case object Neq extends BinOp
        case object Lt extends BinOp
        case object Leq extends BinOp
        case object Gt extends BinOp
        case object Geq extends BinOp

        case object LAnd extends BinOp
        case object LOr extends BinOp
    }
    sealed trait UnOp
    object UnOp {
        case object Minus extends UnOp
        case object Negate extends UnOp
        case object Not extends UnOp
    }
    case class Stmt(ty: Type, name: Option[Ident])
    case class MatchArm(cond: Expr, ty: Type)
}

object Parser {
    import fastparse._, ScalaWhitespace._
    import Ast._

    val keywords = Set("repeat","at","if","in","while","until","for","assert","match")

    def wordlike[_: P]: P0 = P( CharIn("a-zA-Z0-9_") )

    def ident[_: P]: P[Ident] = P( (CharIn("a-zA-Z_") ~~ CharIn("a-zA-Z0-9_").repX).!.filter(!keywords.contains(_)).map(Ident(_)) )
    def num[_: P]: P[Long] = P(
        ("0x" ~~ CharIn("0-9A-Fa-f").repX(1).!.map(s => Try{HexFormat.fromHexDigitsToLong(s)})
        | "0b" ~~ CharIn("01").repX(1).!.map(s => Try{lang.Long.parseLong(s, 2)})
        | "0o" ~~ CharIn("0-7").repX(1).!.map(s => Try{lang.Long.parseLong(s, 8)})
        | CharIn("0-9").repX(1).!.map(s => Try{lang.Long.parseLong(s)})
        ).filter(_.isSuccess).map(_.get) ~~ !wordlike
    )

    def struct[_: P]: P[Type.Struct] = P(("{" ~ stmt.rep ~ "}").map(Type.Struct))
    def matchArm[_: P]: P[MatchArm] = P(
        ("(" ~ expr ~ ")" ~ ":" ~ ty ~ ";").map(Function.tupled(MatchArm))
    )
    def plaintype[_: P]: P[Type] = P(
        ( ident.map(Type.Named)
        | (annotation ~ plaintype).map(Type.Annotated.tupled)
        | struct
        | ("repeat" ~ ty ~ repeatCond).map(Type.Repeated.tupled)
        | ("match" ~ "{" ~ matchArm.rep ~ "}").map(Type.Match)
        | ("assert" ~ "(" ~ expr ~ ")").map(Type.Assert))
    )
    def tyTrail[_: P]: P[Function1[Type, Type]] = P(
        ( "*".!.map(_ => ty => Type.Pointer(ty))
        | ("[" ~ expr ~ "]").map(expr => ty => Type.Array(ty, expr)))
    )
    def ty[_: P]: P[Type] = P(
        ("calc" ~/ "(" ~ expr ~ ")").map(Type.Calc) |
        ("if" ~/ "(" ~ expr ~ ")" ~ ty).map(Type.Conditional.tupled) |
        ("in" ~/ "(" ~ expr ~ ")" ~ ty).map(Type.Inside.tupled) |
        (plaintype ~ tyTrail.rep).map {
            case (t, trails) =>
                trails.foldLeft[Type](t)((acc, p) => p(acc))
        })

    def annotation[_: P]: P[Annotation] = P(
        "@align" ~ "(" ~ num.map(_.toInt).map(Annotation.Align) ~ ")"
        | "@pack".!.map(_ => Annotation.Pack)
    )
    def repeatCond[_: P]: P[RepeatCond] = P(
        ( "eof".!.map(_ => RepeatCond.Eof)
        | ("until" ~ "(" ~ expr ~ ")").map(RepeatCond.Until)
        | ("while" ~ "(" ~ expr ~ ")").map(RepeatCond.While) )
    )

    def trailAtom[_: P]: P[Expr => Expr] = P(
         ("[" ~ expr.map(ix => e => Expr.Index(e, ix)) ~ "]")
        |("." ~ ident.map(p => e => Expr.Prop(e, p))))
    def exprAtom[_: P]: P[Expr] = P(
        ( num.map(Expr.ConstantNum)
        | ("\"" ~~
            ( CharPred(!"\\\"".contains(_)).!.map(_(0).toByte)
            | "\\" ~~ ( "x" ~~ CharIn("0-9a-fA-F").repX(exactly=2).!.map(lang.Byte.parseByte(_, 16))
                      | "n".!.map(_ => '\n'.toByte)
                      | "t".!.map(_ => '\t'.toByte)
                      | "\"".!.map(_ => '"'.toByte))
            ).rep ~~ "\"").map(s => Expr.ConstantBytes(s.toIndexedSeq))
        | ident.map(Expr.Variable)
        | "(" ~ expr ~ ")"
        ) ~ trailAtom.repX
    ).map{
        case (e, trail) =>
            trail.foldLeft[Expr](e){case (l, t) => t(l)}
    }
    def op[_: P](s: String, o: BinOp): ParsingRun[BinOp] = LiteralStr(s).map(_ => o)
    def lassoc[_: P](sub: => P[Expr], o: => P[BinOp]): P[Expr] = P(sub ~ (o ~ sub).rep).map {
        case (lhs, rhss) =>
            rhss.foldLeft(lhs){case (l, (o, r)) => Expr.Binary(l, o, r)}
    }
    def rassoc[_: P](sub: => P[Expr], o: => P[BinOp]): P[Expr] = P(sub ~ (o ~ sub).rep).map {
        case (lhs, rhss) =>
            val all = rhss.prepended((BinOp.Add /*placeholder*/, lhs))
            val lhss = all.sliding(2).filter(_.length == 2).map(a => (a(0)._2, a(1)._1))
            val rhs = all.last._2
            lhss.foldRight(rhs){case ((l, o), r) => Expr.Binary(l, o, r)}
    }
    def mone[_: P](sub: => P[Expr], o: => P[BinOp]): P[Expr] = P(
        (sub ~ o ~ sub).map(Expr.Binary.tupled)
        | sub)

    def unOp[_: P]: P[UnOp] = P("-".!.map(_ => UnOp.Minus) | "~".!.map(_ => UnOp.Negate) | "!".!.map(_ => UnOp.Not))
    def exprUnary[_: P]: P[Expr] = P((unOp ~ exprAtom).map(Expr.Unary.tupled) | exprAtom)
    def binopMul[_: P]: P[BinOp] = P(op("*", BinOp.Mul) | op("/", BinOp.Div) | op("%", BinOp.Mod))
    def exprMul[_: P]: P[Expr] = lassoc(exprUnary, binopMul)
    def binopAdd[_: P]: P[BinOp] = P(op("+", BinOp.Add) | op("-", BinOp.Sub))
    def exprAdd[_: P]: P[Expr] = lassoc(exprMul, binopAdd)
    def binopAnd[_: P]: P[BinOp] = P(op("&", BinOp.And))
    def exprAnd[_: P]: P[Expr] = rassoc(exprAdd, binopAnd)
    def binopXor[_: P]: P[BinOp] = P(op("^", BinOp.Xor))
    def exprXor[_: P]: P[Expr] = rassoc(exprAnd, binopXor)
    def binopOr[_: P]: P[BinOp] = P(op("|", BinOp.Or))
    def exprOr[_: P]: P[Expr] = rassoc(exprXor, binopOr)
    def binopShift[_: P]: P[BinOp] = P(op("<<", BinOp.Shl) | op(">>", BinOp.Shr))
    def exprShift[_: P]: P[Expr] = mone(exprOr, binopShift)
    def binopCmp[_: P]: P[BinOp] = P(op("<=", BinOp.Leq) | op(">=", BinOp.Geq) | op("<", BinOp.Lt) | op(">", BinOp.Gt) | op("==", BinOp.Eq) | op("!=", BinOp.Neq))
    def exprCmp[_: P]: P[Expr] = mone(exprShift, binopCmp)
    def binopLAnd[_: P]: P[BinOp] = P(op("&&", BinOp.LAnd))
    def exprLAnd[_: P]: P[Expr] = rassoc(exprCmp, binopLAnd)
    def binopLOr[_: P]: P[BinOp] = P(op("||", BinOp.LOr))
    def exprLOr[_: P]: P[Expr] = rassoc(exprLAnd, binopLOr)
    def exprTernary[_: P]: P[Expr] = P(
        (exprLOr ~ "?" ~ exprTernary ~ ":" ~ exprTernary).map(Expr.Ternary.tupled) | exprLOr
    )

    def expr[_: P]: P[Expr] = P(
        exprTernary
    )

    def stmt[_: P]: P[Stmt] = P(ty ~ ident.? ~/ ";").map(Stmt.tupled)

    def typedef[_: P]: P[Top] = P(ident ~ ":=" ~/ ty ~/ ";").map(Top.TypeDef.tupled)
    def toplevel[_: P]: P[Seq[Top]] = P("" ~ typedef.rep)
}

object Foo extends App {
    import Parser._
    import fastparse._
    /*val res = parse(raw"""{
        u1 * /* inline /* nested */ comment */ [3] * pointsToArrayOfPointers;
        if (0) u4 optional;
    }""", ty(_))*/
    val s = new FileInputStream("example.struct").readAllBytes()
    //val res = parse("5 >> 2 != 0 ? x : y - y == 0 ? 1 : 0", expr(_), true)
    val res = parse(s, toplevel(_), true, 1202)
    println(res)
    res.fold({case (s, p, extra) =>
        println("Failed")
        println(s, p, extra)
        println(extra.trace(true))
    }, { case (e, p) =>
        println("Success")
        println(e, p)
    })

}