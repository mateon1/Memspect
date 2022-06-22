import java.io.RandomAccessFile
import java.util.HexFormat

object Hello extends App {
    println("Hello, world!")
    println("asdfgasdfg")
    val m = ProcMaps(26440)
    println(m.findArea(0x401350))
    val f = new RandomAccessFile("/proc/self/mem", "r")
    var b = Array.ofDim[Byte](4096)
    var off = 0x82000000L
    f.seek(off)
    while (b.forall(_ == 0)) {
        f.readFully(b)
        off += b.length
    }
    off -= b.length
    println("Bytes at " ++ HexFormat.of.toHexDigits(off))
    //println(b.mkString(", "))
    println(HexFormat.ofDelimiter(" ").formatHex(b))
}


object Mem extends App {
    //println(args)
    //for (a <- args) println(a)
    //val pid = Integer.parseUnsignedInt(args(0))
    val pid = 2686400
    val m = ForeignMemory(pid)
    println(m)
}