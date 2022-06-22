import java.util.HexFormat
import java.lang
import scala.util.Try
import scala.collection.mutable.Stack
import scala.collection.mutable
import Ast.Type.Annotated
import Ast.Type.Named
import Ast.Type.Struct
import Ast.Type.Pointer
import Ast.Type.Repeated
import Ast.Type.Conditional
import Ast.Type.Inside
import Ast.Type.Match
import Ast.Type.Assert
import Ast.Type.Calc
import Ast.Expr.ConstantNum
import Ast.Expr.ConstantBytes
import Ast.Expr.Variable
import Ast.Expr.Ternary
import Ast.Expr.Binary
import Ast.Expr.Unary
import Ast.Expr.Prop
import Ast.Expr.Index
import Ast.RepeatCond.Eof
import Ast.RepeatCond.Until
import Ast.RepeatCond.While
import java.io.InputStream

object Ast {
    case class Ident(name: String)
    sealed trait Top
    object Top {
        case class TypeDef(name: Ident, ty: Type) extends Top
    }
    sealed trait Type
    object Type {
        case class Integer(bytes: Int) extends Type
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
    sealed trait BinOp {
        def apply(lhs: StructVal, rhs: StructVal): Option[StructVal] = lhs.intValue.flatMap(l => rhs.intValue.map((l, _))).map{
            case ((l, r)) => StructVal.PrimInt(this(l, r))
        }
        def apply(lhs: Long, rhs: Long): Long
    }
    object BinOp {
        case object Mul extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs * rhs }
        case object Div extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs / rhs }
        case object Mod extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs % rhs }
        case object Add extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs + rhs }
        case object Sub extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs - rhs }
        case object And extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs & rhs }
        case object Xor extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs ^ rhs }
        case object Or extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs | rhs }
        case object Shl extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs << rhs }
        case object Shr extends BinOp { override def apply(lhs: Long, rhs: Long) = lhs >> rhs }

        case object Eq extends BinOp { override def apply(lhs: Long, rhs: Long) = if (lhs == rhs) 1 else 0 }
        case object Neq extends BinOp { override def apply(lhs: Long, rhs: Long) = if (lhs != rhs) 1 else 0 }
        case object Lt extends BinOp { override def apply(lhs: Long, rhs: Long) = if (lhs < rhs) 1 else 0 }
        case object Leq extends BinOp { override def apply(lhs: Long, rhs: Long) = if (lhs <= rhs) 1 else 0 }
        case object Gt extends BinOp { override def apply(lhs: Long, rhs: Long) = if (lhs > rhs) 1 else 0 }
        case object Geq extends BinOp { override def apply(lhs: Long, rhs: Long) = if (lhs >= rhs) 1 else 0 }

        case object LAnd extends BinOp { override def apply(lhs: Long, rhs: Long) = if ((lhs != 0) && (rhs != 0)) 1 else 0 }
        case object LOr extends BinOp { override def apply(lhs: Long, rhs: Long) = if ((lhs != 0) || (rhs != 0)) 1 else 0 }
    }
    sealed trait UnOp {
        def apply(o: StructVal): Option[StructVal] = o.intValue.map(v => StructVal.PrimInt(this(v)))
        def apply(o: Long): Long
    }
    object UnOp {
        case object Minus extends UnOp { override def apply(o: Long): Long = -o }
        case object Negate extends UnOp { override def apply(o: Long): Long = ~o }
        case object Not extends UnOp { override def apply(o: Long): Long = if (o == 0) 1 else 0 }
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
        ( ("u" ~~ (CharIn("1-9") ~~ CharIn("0-9")).!.map(lang.Integer.parseUnsignedInt(_)).map(Type.Integer))
        | ident.map(Type.Named)
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

    def typedef[_: P]: P[Top.TypeDef] = P(ident ~ ":=" ~/ ty ~/ ";").map(Top.TypeDef.tupled)
    def typedefs[_: P]: P[Seq[Top.TypeDef]] = P("" ~ typedef.rep)
    def toplevel[_: P]: P[Seq[Top]] = typedefs

    def parseProgram(inp: fastparse.ParserInputSource): Parsed[Seq[Top.TypeDef]] = parse(inp, typedefs(_))
}

sealed trait StructVal {
    var replaced = Option.empty[StructVal]
    val vals = mutable.ArrayBuffer[StructVal]()
    val valNames = mutable.HashMap[String, Int]()
    var spanStart = Option.empty[Long]
    var spanEnd = Option.empty[Long]
    def apply(idx: Int): Option[StructVal] = Option.empty
    def builtinProp(prop: String): Option[StructVal] = {
        Option(prop match {
            case "length" => StructVal.PrimInt(vals.length.toLong)
            case _ => return Option.empty
        })
    }
    def apply(prop: String): Option[StructVal] = {
        valNames.get(prop).map(vals(_)).orElse(builtinProp(prop))
    }
    def push(o: StructVal, name: Option[String]) = {
        vals.addOne(o)
        for (n <- name) valNames.addOne((n, vals.length - 1))
    }
    def replace(o: StructVal) = replaced = Option(o)
    def intValue: Option[Long] = replaced.flatMap(_.intValue)
}
object StructVal {
    // ...
    case class Object() extends StructVal
    case class PrimInt(v: Long) extends StructVal { override def intValue = Option(v) }
    case class PrimBytes(v: IndexedSeq[Byte]) extends StructVal { override def apply(idx: Int) = Option.when(idx < v.size)(StructVal.PrimInt(v(idx).toLong)) }
}
class StructCtx(val defs: Map[String, Ast.Type], val vals: mutable.Map[String, StructVal], val parent: Option[StructCtx], val self: StructVal) {
    def resolveName(id: Ast.Ident): Option[StructVal] = {
        vals.get(id.name).orElse(parent.flatMap(_.resolveName(id)))
    }
    def resolveType(id: Ast.Ident): Option[Ast.Type] = defs.get(id.name)
    private def child(obj: StructVal) = new StructCtx(defs, mutable.HashMap.empty, Option(this), obj)
    private def child(name: Option[String]): StructCtx = {
        val subobj = StructVal.Object()
        self.push(subobj, name)
        child(subobj)
    }
    private def child(name: String): StructCtx = child(Option(name))
    private def child(): StructCtx = child(Option.empty)
    def parse(mem: ForeignMemory, offs: Long, ty: Ast.Type): Option[Long] = {
        ty match {
            case Ast.Type.Integer(bytes) => throw new NotImplementedError
            case Annotated(annot, ty) => parse(mem, offs, ty) // TODO: Make this functional
            case Named(name) => resolveType(name).flatMap(parse(mem, offs, _))
            case Struct(body) => // TODO: Alignment
                body.foldLeft(Option(offs)){ case (res, stmt) => res.flatMap { case offs =>
                        child(stmt.name.map(_.name)).parse(mem, offs, stmt.ty)
                    }
                }
            case Pointer(to) => throw new NotImplementedError
            case Ast.Type.Array(of, len) => this.eval(len).flatMap(_.intValue).flatMap{
                case reps =>
                    (1.to(reps.toInt)).foldLeft(Option(offs)){case (o, _) => o.flatMap(child().parse(mem, _, of))}
            }
            case Repeated(what, cond) => {
                var curoffs = offs
                do {
                    child().parse(mem, curoffs, what) match {
                        case None => return None
                        case Some(value) => curoffs = value
                    }
                } while ((cond match {
                    case Eof => Option(false)
                    case Until(pred) => eval(pred).flatMap(_.intValue).map(_ == 0)
                    case While(pred) => eval(pred).flatMap(_.intValue).map(_ != 0)
                }) match {
                    case None => return None
                    case Some(bool) => bool
                })
                Option(curoffs)
            }
            case Conditional(cond, ty) => eval(cond).flatMap(_.intValue).flatMap(c => if (c == 0) Option(offs) else parse(mem, offs, ty))
            case Inside(buf, ty) => throw new NotImplementedError
            case Match(arms) => {
                for (a <- arms) {
                    eval(a.cond).flatMap(_.intValue) match {
                        case None => return None
                        case Some(0) => ()
                        case Some(_) => return parse(mem, offs, a.ty) 
                    }
                }
                None
            }
            case Assert(pred) => eval(pred).flatMap(_.intValue).filter(_ != 0).map(_ => offs)
            case Calc(expr) => eval(expr).map(v => self.replace(v)).map(_ => offs)
        }
    }
    def eval(e: Ast.Expr): Option[StructVal] = {
        e match {
            case ConstantNum(value) => Option(StructVal.PrimInt(value))
            case ConstantBytes(value) => Option(StructVal.PrimBytes(value))
            case Variable(name) => resolveName(name)
            case Ternary(cond, left, right) => eval(cond).flatMap(_.intValue).flatMap(c => if (c != 0) eval(left) else eval(right))
            case Binary(left, op, right) => eval(left).flatMap(l => eval(right).flatMap(op.apply(l, _)))
            case Unary(op, of) => eval(of).flatMap(op.apply)
            case Prop(obj, name) => eval(obj).flatMap(_(name.name))
            case Index(arr, idx) => eval(arr).flatMap(a => eval(idx).flatMap(_.intValue).flatMap(v => a(v.toInt)))
        }
    }
    vals.addOne(("_", self))
}
object StructCtx {
    import Ast._
    def apply(defs: Seq[Top.TypeDef]): StructCtx = {
        val root = StructVal.Object()
        val ctx = new StructCtx(defs.map(x => (x.name.name, x.ty)).toMap, mutable.HashMap(("root", root)), Option.empty, root)
        ctx
    }
}

object Foo extends App {
    import Parser._
    import fastparse._
    import java.io.FileInputStream
    /*val res = parse(raw"""{
        u1 * /* inline /* nested */ comment */ [3] * pointsToArrayOfPointers;
        if (0) u4 optional;
    }""", ty(_))*/
    val s = new FileInputStream("example.struct").readAllBytes()
    //val res = parse("5 >> 2 != 0 ? x : y - y == 0 ? 1 : 0", expr(_), true)
    val res = parse(s, toplevel(_), true)
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