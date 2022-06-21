
/*
Language overview

Define elements:

weirdStruct := {
    u16 major;
    assert (major == 1); // stop parsing on unexpected data
    u16; // name optional
    // automatic align unless overridden with @pack or @align(n)
    otherType*[4] arr; // arrays and pointers (complex types always innermost left to outermost right)
    // this means indexing arr[5][10] requires the array is (at least) type[11][6]
    @pack { u16; u8; } inlineStruct;
    repeat u8 until (_ == 0); // array of unspecified size, parens mandatory
    repeat {
        u8 tag;
        if (tag != 0) varint len;
        if (tag != 0) u8[len.val] raw;
        if (tag != 0) match { // u8 buffers can be reused as things to reparse -- NOTE: does this make pointers relative to the new buffer?
            (tag == 1): in(raw) repeat u8 eof;
            (tag == 2): in(raw) repeat varint eof;
            (tag == 3): in(raw) randomComplexType;
            // fallthrough automatically fails to parse
        } parsed;
    } until (_.tag == 0) selfTerminatedTlvArray;
    repeat repeat u8 until (_ == 0) until (_.length == 1) stringTable;
    // TODO: at(<object base>[+offset]) type;
    // maybe at(addr) and provide .base on objects (how does this interact with in(..)?)
}

varint := @pack {
    repeat u8 until (_ & 0x80 == 0) raw;
    assert (raw.length);
    calc (
        u8 val = 0;
        for (e <- raw) val = (val << 7) | e & 0x7f;
        val
    ) value;
}
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
        case class Array(of: Type, len: Int) extends Type
        case class Repeated(what: Type, cond: RepeatCond) extends Type
        case class Conditional(cond: Expr, ty: Type) extends Type
        case class Match(arms: Seq[MatchArm]) extends Type
        case class Assert(pred: Expr) extends Type
    }
    sealed trait Annotation
    object Annotation {
        case class Align(alignment: Int) extends Annotation
        case class Pack() extends Annotation
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
    }
    sealed trait BinOp
    object BinOp {
        case object And extends BinOp
        case object Or extends BinOp
        case object Xor extends BinOp
        case object Add extends BinOp
        case object Sub extends BinOp
        case object Shl extends BinOp
        case object Shr extends BinOp

        case object Eq extends BinOp
        case object Neq extends BinOp
        case object Lt extends BinOp
        case object Leq extends BinOp
        case object Gt extends BinOp
        case object Geq extends BinOp
    }
    sealed trait UnOp
    object UnOp {
        case object Minus extends UnOp
        case object Negate extends UnOp
    }
    case class Stmt(ty: Type, name: Option[Ident])
    case class MatchArm(cond: Expr, ty: Type)
}

object Foo extends App {
    import fastparse._, MultiLineWhitespace._
    import Ast._

    def ident[_: P]: P[Ident] = P( (CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_")).!.map(Ident(_)) )

    //def struct[_: P]: P[Struct] = P( ident )
    //def typ[_: P]: P[AnyType] = P( ident | struct )
    //def typ[_: P]: P[?]
    ParserInput
    val res = parse("abcdefg", ident(_))
    println(res)
}