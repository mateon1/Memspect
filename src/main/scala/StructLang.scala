import scala.collection.mutable
import scala.collection.immutable
import RandomAccess._
import java.io.FileNotFoundException

object Ast {
    case class Ident(name: String)
    sealed trait Endianness
    object Endianness {
        case object Big extends Endianness
        case object Little extends Endianness
    }
    sealed trait Top
    object Top {
        case class TypeDef(name: Ident, ty: Type) extends Top
    }
    sealed trait Type {
        protected def fitPowTwo(x: Int): Int = {
            assert(x > 0)
            var t = x - 1 // subtract one, so if it's already a power of two, don't change it
            t = t | (t >> 1) // smear ones all over the least significant bits
            t = t | (t >> 2)
            t = t | (t >> 4)
            t = t | (t >> 8)
            t = t | (t >> 16) // it's now 2^k-1
            t + 1 // and now 2^k
        }
        val naturalAlignment: Option[Int] = None
    }
    object Type {
        import Annotation._
        case class Integer(bytes: Int, endian: Option[Endianness]) extends Type { override val naturalAlignment: Option[Int] = Some(fitPowTwo(bytes)) }
        case class Annotated(annot: Annotation, ty: Type) extends Type {
            override val naturalAlignment: Option[Int] = annot match {
                case Align(alignment) => Some(alignment)
                case Pack => Some(1) // @pack needs to be handled separately anyway, as it overrides alignment for all children
                case Lookahead => None
                case Try => None
            }
        }
        case class Named(name: Ident) extends Type
        case class Struct(body: Seq[Stmt]) extends Type { override val naturalAlignment: Option[Int] = body.flatMap(s => s.ty.naturalAlignment).maxOption }
        case class Pointer(to: Type) extends Type { override val naturalAlignment: Option[Int] = Some(8) }
        case class Array(of: Type, len: Expr) extends Type { override val naturalAlignment: Option[Int] = of.naturalAlignment }
        case class Repeated(what: Type, cond: RepeatCond) extends Type { override val naturalAlignment: Option[Int] = what.naturalAlignment }
        case class Conditional(cond: Expr, ty: Type) extends Type
        case class Inside(buf: Expr, ty: Type) extends Type
        case class At(offs: Expr, ty: Type) extends Type
        case class Match(arms: Seq[MatchArm]) extends Type
        case class Assert(pred: Expr) extends Type
        case class Calc(expr: Expr) extends Type
    }
    sealed trait Annotation
    object Annotation {
        case class Align(alignment: Int) extends Annotation
        case object Pack extends Annotation
        case object Lookahead extends Annotation
        case object Try extends Annotation
    }
    sealed trait RepeatCond
    object RepeatCond {
        case object Eof extends RepeatCond
        case class Until(pred: Expr) extends RepeatCond
        case class While(pred: Expr) extends RepeatCond
    }
    sealed trait Expr
    object Expr {
        case class ConstantNum(value: BigInt) extends Expr
        case class ConstantBytes(value: Seq[Byte]) extends Expr
        case object Nil extends Expr
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
        def apply(lhs: BigInt, rhs: BigInt): BigInt = 0
    }
    object BinOp {
        case object Mul extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = lhs * rhs }
        case object Div extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = lhs / rhs }
        case object Mod extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = lhs % rhs }
        case object Add extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = lhs + rhs }
        case object Sub extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = lhs - rhs }
        case object And extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = lhs & rhs }
        case object Xor extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = lhs ^ rhs }
        case object Or extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = lhs | rhs }
        case object Shl extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = { assert(rhs.isValidInt); lhs << rhs.toInt } }
        case object Shr extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = { assert(rhs.isValidInt); lhs >> rhs.toInt } }

        case object Eq extends BinOp { override def apply(lhs: StructVal, rhs: StructVal): Option[StructVal] = { Some(StructVal.PrimInt(if (lhs == rhs) 1 else 0)) } }
        case object Neq extends BinOp { override def apply(lhs: StructVal, rhs: StructVal): Option[StructVal] = { Some(StructVal.PrimInt(if (lhs != rhs) 1 else 0)) } }
        case object Lt extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = if (lhs < rhs) 1 else 0 }
        case object Leq extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = if (lhs <= rhs) 1 else 0 }
        case object Gt extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = if (lhs > rhs) 1 else 0 }
        case object Geq extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = if (lhs >= rhs) 1 else 0 }

        case object LAnd extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = if ((lhs != 0) && (rhs != 0)) 1 else 0 }
        case object LOr extends BinOp { override def apply(lhs: BigInt, rhs: BigInt) = if ((lhs != 0) || (rhs != 0)) 1 else 0 }
    }
    sealed trait UnOp {
        def apply(o: StructVal): Option[StructVal] = o.intValue.map(v => StructVal.PrimInt(this(v)))
        def apply(o: BigInt): BigInt
    }
    object UnOp {
        case object Minus extends UnOp { override def apply(o: BigInt): BigInt = -o }
        case object Negate extends UnOp { override def apply(o: BigInt): BigInt = ~o }
        case object Not extends UnOp { override def apply(o: BigInt): BigInt = if (o == 0) 1 else 0 }
    }
    case class Stmt(ty: Type, name: Option[Ident])
    case class MatchArm(cond: Expr, ty: Type)
}

object Parser {
    import fastparse._, ScalaWhitespace._
    import Ast._
    import java.lang

    val keywords = Set("repeat","at","if","in","while","until","for","assert","match","calc","nil")

    def wordlike[_: P]: P0 = P( CharIn("a-zA-Z0-9_") )

    def ident[_: P]: P[Ident] = P( (CharIn("a-zA-Z_") ~~ CharIn("a-zA-Z0-9_").repX).!.filter(!keywords.contains(_)).map(Ident(_)) )
    def num[_: P]: P[BigInt] = P(
        ("0x" ~~ CharIn("0-9A-Fa-f").repX(1).!.map(BigInt(_, 16))
        | "0b" ~~ CharIn("01").repX(1).!.map(BigInt(_, 2))
        | "0o" ~~ CharIn("0-7").repX(1).!.map(BigInt(_, 8))
        | CharIn("0-9").repX(1).!.map(BigInt(_))
        | "'" ~~ bytestrchar.map(BigInt(_)) ~~ "'"
        ) ~~ !wordlike
    )

    def bytestrchar[_: P]: P[Byte] = P(
        ("\\x" ~~ CharIn("0-9a-fA-F").repX(exactly=2).!.map(lang.Integer.parseUnsignedInt(_, 16).toByte)
        | "\\n".!.map(_ => '\n'.toByte)
        | "\\t".!.map(_ => '\t'.toByte)
        | "\\r".!.map(_ => '\r'.toByte)
        | "\\\"".!.map(_ => '"'.toByte)
        | CharIn(" !#-[]-~").!.map(_(0).toByte) // printable ascii except '"' and '\'
        )
    )

    def bytestr[_: P]: P[Expr.ConstantBytes] = P(
        "\"" ~~ bytestrchar.repX.map(bs => Expr.ConstantBytes(bs)) ~~ "\""
    )

    def struct[_: P]: P[Type.Struct] = P(("{" ~ stmt.rep ~ "}").map(Type.Struct))
    def matchArm[_: P]: P[MatchArm] = P(
        ("(" ~ expr ~ ")" ~ ":" ~ ty ~ ";").map(Function.tupled(MatchArm))
    )
    def plaintype[_: P]: P[Type] = P(
        ( (("u" ~~
                (CharIn("1-9") ~~ CharIn("0-9").repX).!.map(lang.Integer.parseUnsignedInt(_)) ~~
                (("be".!.map(_ => Endianness.Big) | "le".!.map(_ => Endianness.Little)).?)
            ).map(Type.Integer.tupled))
        | ident.map(Type.Named)
        | (annotation ~ plaintype).map(Type.Annotated.tupled)
        | struct
        | ("calc" ~ "(" ~/ expr ~ ")").map(Type.Calc)
        | ("repeat" ~ ty ~ repeatCond).map(Type.Repeated.tupled)
        | ("match" ~ "{" ~ matchArm.rep ~ "}").map(Type.Match)
        | ("assert" ~ "(" ~ expr ~ ")").map(Type.Assert))
        | "(" ~ ty ~ ")"
    )
    def tyTrail[_: P]: P[Function1[Type, Type]] = P(
        ( "*".!.map(_ => ty => Type.Pointer(ty))
        | ("[" ~ expr ~ "]").map(expr => ty => Type.Array(ty, expr)))
    )
    def ty[_: P]: P[Type] = P(
        ("if" ~ "(" ~/ expr ~ ")" ~ ty).map(Type.Conditional.tupled) |
        ("in" ~ "(" ~/ expr ~ ")" ~ ty).map(Type.Inside.tupled) |
        ("at" ~ "(" ~/ expr ~ ")" ~ ty).map(Type.At.tupled) |
        (plaintype ~ tyTrail.rep).map {
            case (t, trails) =>
                trails.foldLeft[Type](t)((acc, p) => p(acc))
        })

    def annotation[_: P]: P[Annotation] = P(
        "@align" ~ "(" ~ num.map(_.toInt).filter(a => a != 0 && (a & (a-1)) == 0 ).map(Annotation.Align) ~ ")"
        | "@pack".!.map(_ => Annotation.Pack)
        | "@lookahead".!.map(_ => Annotation.Lookahead)
        | "@try".!.map(_ => Annotation.Try)
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
        ( "nil".!.map(_ => Expr.Nil)
        | num.map(Expr.ConstantNum)
        | bytestr
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
        "" ~ exprTernary ~ ""
    )

    def stmt[_: P]: P[Stmt] = P(ty ~ ident.? ~/ ";").map(Stmt.tupled)

    def typedef[_: P]: P[Top.TypeDef] = P(ident ~ ":=" ~/ ty ~/ ";").map(Top.TypeDef.tupled)
    def typedefs[_: P]: P[Seq[Top.TypeDef]] = P("" ~ typedef.rep)
    def toplevel[_: P]: P[Seq[Top]] = typedefs

    def parseProgram(inp: fastparse.ParserInputSource): Parsed[Seq[Top.TypeDef]] = parse(inp, typedefs(_))
}

sealed trait StructVal extends RandomAccess {
    var replaced = Option.empty[StructVal]
    val vals = mutable.ArrayBuffer[StructVal]()
    val valNames = mutable.SeqMap[String, Int]()
    val valUnnamed = mutable.ArrayBuffer[Int]()
    var spanStart = Option.empty[Long]
    var spanEnd = Option.empty[Long]
    var last = Option.empty[StructVal]
    def withSpan(from: Long, to: Long): StructVal = {
        spanStart = Option(from)
        spanEnd = Option(to)
        this
    }
    def apply(idx: Int): Option[StructVal] = {
        for (r <- replaced) return r(idx)
        Option.when(idx < valUnnamed.length)(vals(valUnnamed(idx)))
    }
    protected def builtinProp(prop: String): Option[StructVal] = {
        prop match {
            case "length" => Some(StructVal.PrimInt(BigInt(valUnnamed.length)))
            case "last" => last
            case _ => Option.empty
        }
    }
    def apply(prop: String): Option[StructVal] = {
        for (r <- replaced) return r(prop)
        valNames.get(prop).map(vals(_)).orElse(builtinProp(prop))
    }
    def push(o: StructVal, name: Option[String]): Unit = {
        for (r <- replaced) return r.push(o, name)
        val idx = vals.length
        vals.addOne(o)
        last = Some(o)
        name match {
            case None => valUnnamed.addOne(idx)
            case Some(n) => valNames.addOne((n, idx))
        }
    }
    def replace(o: StructVal) = replaced = Option(o)
    def intValue: Option[BigInt] = replaced.flatMap(_.intValue)
    def read(offs: Long, maxlen: Int): Option[Array[Byte]] = {
        for (r <- replaced) return r.read(offs, maxlen)
        Option.when(offs <= valUnnamed.length)(valUnnamed.slice(offs.toInt, offs.toInt + maxlen).map(vals(_).intValue))
            .filter(a => { a.map(v => v.isDefined && (v.get & ~0xff) == 0).minOption != Some(false) })
            .map(a => a.map(_.get.toByte).toArray)
    }
    override def toString(): String = {
        for (r <- replaced) return r.toString()
        val names = valNames.map{case((a, b)) => (b, a)}
        val subs = vals.zipWithIndex.map{case (v, i) => (names.get(i) match { case Some(n) => n + ": "; case None => "" }) + v.toString() + "; "}
        val span = for (start <- spanStart; end <- spanEnd) yield f"<$start%d..$end%d>"
        val printables = BigInt(32).to(126)
        () match {
            case () if intValue.isDefined && subs.isEmpty => intValue.get.toString()
            case () if names.isEmpty && vals.zipWithIndex.map{case((v, i)) => v.intValue.isDefined && (i > 0 && i == vals.length - 1 && v.intValue.get == 0 || v.intValue.get == '\t' || v.intValue.get == '\n' || printables.contains(v.intValue.get))}.minOption == Some(true)
                => span.map(_ + " ").getOrElse("") + "\"" + vals.map(_.intValue.get.toByte match {
                    case '\n' => "\n"
                    case '\t' => "\t"
                    case 0 => "\\x00"
                    case v => v.toChar.toString()
                }).mkString + "\""
            case () =>
                span.map(_ + " ").getOrElse("") +
                Option.when(subs.nonEmpty)("{ " + subs.mkString + "}").getOrElse("nil") +
                intValue.map(" = " + _).getOrElse("")
        }
        /*
        /*"StructVal::" + this.getClass().getSimpleName() + "[" + valUnnamed.length + "] { "*/ "{ " + subs.mkString + "}" + (intValue match {
            case None => ""
            case Some(value) => " = " + value
        })*/
    }
    override def equals(obj: Any): Boolean = {
        for (r <- replaced) return r.equals(obj)
        if (!obj.isInstanceOf[StructVal]) return false
        val rhs = obj.asInstanceOf[StructVal]
        // TODO: How to handle lazy values?
        (this.valNames.keySet == rhs.valNames.keySet
        && this.valUnnamed.length == rhs.valUnnamed.length
        && this.intValue == rhs.intValue
        && this.valNames.foldLeft(true){case (b, (key, lIdx)) =>
            b && {
                val rIdx = rhs.valNames(key)
                this.vals(lIdx) == rhs.vals(rIdx)
            }
        } && this.valUnnamed.zip(rhs.valUnnamed).foldLeft(true){case (b, (lIdx, rIdx)) =>
            b && this.vals(lIdx) == rhs.vals(rIdx)
        })
    }
}
object StructVal {
    // ...
    case class Object() extends StructVal
    case class PrimInt(v: BigInt) extends StructVal { override def intValue = Option(v) }
    // This sucks for performance (or does it?) but makes equality work consistently at least
    object PrimBytes {
        def apply(vs: Seq[Byte]): StructVal = {
            val o = StructVal.Object()
            for (v <- vs) o.push(StructVal.PrimInt(v & 0xff), None)
            o
        }
    }
    case class LazyVal(ctx: StructCtx, mem: RandomAccess, offs: BigInt, ty: Ast.Type) extends StructVal {
        private var isParsed = false
        override def apply(prop: String): Option[StructVal] = {
            for (r <- replaced) return r(prop)
            prop match {
                case "parsed" => return Some(StructVal.PrimInt(if (isParsed) 1 else 0))
                case "offset" => return Some(StructVal.PrimInt(offs))
                case _ => ()
            }
            if (!isParsed) doParse()
            super.apply(prop)
        }
        override def apply(idx: Int): Option[StructVal] = {
            for (r <- replaced) return r(idx)
            if (!isParsed) doParse()
            super.apply(idx)
        }
        override def toString(): String = {
            for (r <- replaced) return r.toString()
            if (isParsed)
                super.toString()
            else
                f"<lazy @0x$offs%x>"
        }
        def doParse() {
            assert(ctx.self == this)
            isParsed = true
            ctx.parse(mem, offs.toLong, ty)
        }
    }
}
class StructCtx(val defs: Map[String, Ast.Type], val vals: mutable.Map[String, StructVal], val parent: Option[StructCtx], val self: StructVal, var isolated: Boolean = false) {
    import Ast._
    def resolveName(id: Ast.Ident): Option[StructVal] = {
        vals.get(id.name).orElse(self(id.name)).orElse(parent.filter(_ => !isolated).flatMap(_.resolveName(id)))
    }
    def resolveType(id: Ast.Ident): Option[Ast.Type] = defs.get(id.name)
    var packed = false
    def pack(): Boolean = packed || parent.map(_.pack()).getOrElse(false)
    var tracing = false
    def traced(): StructCtx = { tracing = true; this }
    def trace(): Boolean = tracing || parent.map(_.trace()).getOrElse(false)
    var defaultEndian = Option.empty[Endianness]
    def getDefaultEndian(): Endianness = defaultEndian.getOrElse(parent.map(_.getDefaultEndian).getOrElse(Endianness.Little))

    private def child(obj: StructVal, isolated: Boolean) = new StructCtx(defs, mutable.HashMap.empty, Option(this), obj, isolated)
    private def child(name: Option[String], isolated: Boolean): StructCtx = {
        val subobj = StructVal.Object()
        self.push(subobj, name)
        child(subobj, isolated)
    }
    private def child(name: String, isolated: Boolean): StructCtx = child(Option(name), isolated)
    private def child(isolated: Boolean = false): StructCtx = child(Option.empty, isolated)
    def parse(mem: RandomAccess, startOffs: Long, ty: Ast.Type): Option[Long] = {
        import Type._
        import Ast.Endianness._
        import Ast.Annotation._
        if (trace) println("Parsing " + ty.toString())
        var offs = startOffs
        if (!pack()) {
            for (a <- ty.naturalAlignment; if (a > 0))
                offs += Math.floorMod(-offs, a)
        }
        ty match {
            case Ast.Type.Integer(bytes, endian) => mem.read(offs, bytes).filter(_.length == bytes).map(a => {
                self.withSpan(offs, offs + bytes).replace(StructVal.PrimInt(BigInt(1, endian.getOrElse(getDefaultEndian) match {
                    case Big => a
                    case Little => a.reverse
                })))
                offs + bytes
            })
            case Annotated(annot, ty) => annot match {
                case Align(alignment) => parse(mem, offs, ty) // already handled by natural alignment
                case Pack => { packed = true; parse(mem, offs, ty) }
                case Lookahead => parse(mem, offs, ty).map(_ => offs)
                case Try => parse(mem, offs, ty).orElse(Some(offs))
            }
            case Named(name) => {
                isolated = true // can't resolve names outside lexical scope, still needs to be parent for attributes and such
                resolveType(name).flatMap(parse(mem, offs, _))
            }
            case Struct(body) =>
                body.foldLeft(Option(offs)){ case (res, stmt) => res.flatMap { case offs =>
                        child(stmt.name.map(_.name), false).parse(mem, offs, stmt.ty)
                    }
                }.map(end => { if (offs < end) self.withSpan(offs, end); end })
            // TODO: Actual lazy pointer type, not just alias for an integer
            case Pointer(to) => mem.read(offs, 8).filter(_.length == 8).map(v => self.withSpan(offs, offs + 8).replace(StructVal.LazyVal(this, mem, BigInt(1, getDefaultEndian() match {
                case Big => v
                case Little => v.reverse
            }), to))).map(_ => offs + 8)
            case At(off, ty) => eval(off).flatMap(_.intValue).map(v => self.replace(StructVal.LazyVal(this, mem, v, ty))).map(_ => offs)
            case Ast.Type.Array(of, len) => this.eval(len).flatMap(_.intValue).flatMap{
                case reps =>
                    (1.to(reps.toInt)).foldLeft(Option(offs)){case (o, _) => o.flatMap(child().parse(mem, _, of))}.map(end => { if (offs < end) self.withSpan(offs, end); end })
            }
            case Repeated(what, cond) => {
                var curoffs = offs
                do {
                    child().parse(mem, curoffs, what) match {
                        case None => return None
                        case Some(value) => curoffs = value
                    }
                } while ((cond match {
                    case RepeatCond.Eof => Option(false)
                    case RepeatCond.Until(pred) => eval(pred).flatMap(_.intValue).map(_ == 0)
                    case RepeatCond.While(pred) => eval(pred).flatMap(_.intValue).map(_ != 0)
                }) match {
                    case None => return None
                    case Some(bool) => bool
                })
                if (offs < curoffs) self.withSpan(offs, curoffs)
                Option(curoffs)
            }
            case Conditional(cond, ty) => eval(cond).flatMap(_.intValue).flatMap(c => if (c == 0) Option(offs) else parse(mem, offs, ty))
            case Inside(buf, ty) => eval(buf).map(parse(_, 0, ty)).map(_ => offs)
            case Match(arms) => {
                for (a <- arms) {
                    eval(a.cond).flatMap(_.intValue.map(_ != 0)) match {
                        case None => return None
                        case Some(false) => ()
                        case Some(true) => return parse(mem, offs, a.ty) 
                    }
                }
                None
            }
            case Assert(pred) => eval(pred).flatMap(_.intValue).filter(_ != 0).map(_ => offs)
            case Calc(expr) => eval(expr).map(v => self.replace(v)).map(_ => offs)
        }
    }
    def eval(e: Expr): Option[StructVal] = {
        import Expr._
        if (trace) println("Evaling " ++ e.toString())
        def truev = StructVal.PrimInt(1)
        def falsev = StructVal.PrimInt(0)
        val ret = e match {
            case ConstantNum(value) => Some(StructVal.PrimInt(value))
            case ConstantBytes(value) => Some(StructVal.PrimBytes(value))
            case Nil => Some(StructVal.Object())
            case Variable(name) => resolveName(name)
            case Ternary(cond, left, right) => eval(cond).flatMap(_.intValue).flatMap(c => if (c != 0) eval(left) else eval(right))
            case Binary(left, BinOp.LAnd, right) => eval(left).flatMap(_.intValue).flatMap(v => if (v != 0) eval(right).flatMap(_.intValue).map(r => if (r != 0) truev else falsev) else Some(falsev))
            case Binary(left, BinOp.LOr, right) => eval(left).flatMap(_.intValue).flatMap(v => if (v == 0) eval(right).flatMap(_.intValue).map(r => if (r != 0) truev else falsev) else Some(truev))
            case Binary(left, op, right) => eval(left).flatMap(l => eval(right).flatMap(op.apply(l, _)))
            case Unary(op, of) => eval(of).flatMap(op.apply)
            case Prop(obj, name) => eval(obj).flatMap(_(name.name))
            case Index(arr, idx) => eval(arr).flatMap(a => eval(idx).flatMap(_.intValue).flatMap(v => a(v.toInt)))
        }
        if (trace) println("Evaled " ++ e.toString() ++ " = " ++ ret.toString())
        ret
    }
    def evalExpr(e: String): Option[StructVal] = {
        fastparse.parse(e, Parser.expr(_)).fold((_, _, _) => None, (expr, end) => Option.when(end == e.length)(expr).flatMap(eval))
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
    //println(res)
    res.fold({case (ex, p, extra) =>
        println("Failed")
        println(ex, p, extra)
        println(s.slice(p, p+20).map(_.toChar).mkString)
        println(extra.trace(true))
    }, { case (e, p) =>
        println("Success")
        //println(e, p)
    })

    val defs = parse(s, typedefs(_)).get.value
    val types = immutable.HashMap.from(defs.map(d => (d.name.name, d.ty)))

    val ctx = StructCtx(defs)
    ctx.tracing = true
    val parseres = ctx.parse(Array[Byte](0xd5.toByte, 0xaa.toByte, 0xd5.toByte, 0x2a.toByte), 0, types("varint"))
    println(parseres)

    println(ctx.self)
    println(ctx.self.valNames)
    println(ctx.self.vals)

    val helper = ctx.self("helper").get
    helper.valUnnamed.map(helper.vals(_)).foreach(sv =>
        println(".. [" + sv("idx").flatMap(_.intValue) + "] " + sv("value").flatMap(_.intValue))
    )
    println(ctx.self("value").flatMap(_.intValue))

    val calcTy = parse("""@align(0x20) { calc("abcdef" == "abcdef"); @try u1 test; calc(test == nil); }""", ty(_)).get.value
    val calcCtx = StructCtx(Seq.empty).traced()
    println(calcCtx.parse(Array.emptyByteArray, 3, calcTy))
    println(calcCtx.self)

    val inTy = parse("""in("\x15\x01\x00\x00") u4be""", ty(_)).get.value
    val inCtx = StructCtx(Seq.empty).traced()
    println(inCtx.parse(Array.emptyByteArray, 3, inTy))
    println(inCtx.self)

    println(ctx.evalExpr(""" "test string\x01\x00\nHello!" """))
    println(ctx.evalExpr(""" "" == nil """))

    val ctxDec = StructCtx(Seq.empty).traced()
    println(ctxDec.parse("-61234".map(_.toByte).toArray, 0, types("decimal")))
    println(ctxDec.self)

    val quietCtx = StructCtx(Seq.empty)

    try {
        val ctxXcf = StructCtx(defs).traced()
        println(ctxXcf.parse(new FileInputStream("/tmp/example.xcf").readAllBytes(), 0, types("gimpxcf")))
        println(ctxXcf.self)
    } catch {
        case _: FileNotFoundException => println("Could not load /tmp/example.xcf")
    }
}