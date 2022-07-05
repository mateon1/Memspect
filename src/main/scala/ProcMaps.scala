import Helper._
import scala.collection.immutable.ArraySeq
import java.util.HexFormat
import java.io.RandomAccessFile

case class AddressRange(low: Long, high: Long) extends Ordered[AddressRange] {
    val length = high - low
    override def compare(that: AddressRange): Int = {
        import scala.math.Ordered.orderingToOrdered
        // Offset by Long.MinValue so things like the vsyscall area at the end of the address space sort properly
        (low + Long.MinValue, length + Long.MinValue) compare (that.low + Long.MinValue, that.length + Long.MinValue)
    }
}
object AddressRange {
    def apply(s: Array[Byte]): AddressRange = {
        val (list, rest) = splitByLim[Byte](s, '-', 2)
        assert(rest.isEmpty)
        AddressRange(parseHexInt(list(0)), parseHexInt(list(1)))
    }
}
case class MapFlags(readable: Boolean, writable: Boolean, executable: Boolean, shared: Boolean) {
    def isPrivate: Boolean = !shared
    override def toString(): String = {
        (if (readable) "r" else "-") + (if (writable) "w" else "-")  + (if (executable) "x" else "-") + (if (shared) "s" else "p")
    }
}
object MapFlags {
    def apply(s: Array[Byte]): MapFlags = {
        assert(s.length == 4)
        assert(s(0) == 'r' || s(0) == '-')
        assert(s(1) == 'w' || s(1) == '-')
        assert(s(2) == 'x' || s(2) == '-')
        assert(s(3) == 's' || s(3) == 'p')
        MapFlags(s(0) == 'r', s(1) == 'w', s(2) == 'x', s(3) == 's')
    }
}
case class Device(maj: Int, min: Int)
object Device {
    def apply(s: Array[Byte]): Device = {
        val (list, rest) = splitByLim[Byte](s, ':', 2)
        assert(rest.isEmpty)
        Device(parseLong(list(0), 10).toInt, parseLong(list(1), 10).toInt)
    }
}

case class MapArea(addr: AddressRange, flags: MapFlags, fileOffset: Long, dev: Device, inode: Long, path: Option[String]) {
    override def toString(): String = {
        val fields = f"${addr.low}%08x-${addr.high}%08x ${flags} $fileOffset%08x ${dev.maj}%02d:${dev.min}%02d $inode%d"
        path.map(f"$fields%-72s " + _).getOrElse(fields + " ")
    }
}
object MapArea {
    def apply(s: Array[Byte]): MapArea = {
        val (list, rest) = splitByLim[Byte](s, ' ', 5)
        val path = rest.dropWhile(_ == ' ')
        MapArea(
            AddressRange(list(0)),
            MapFlags(list(1)),
            parseHexInt(list(2)),
            Device(list(3)),
            parseLong(list(4), 10),
            Option.unless(path.length == 0)(String.valueOf(path.map(_.toChar)))
        )
    }
}

class ProcMaps(maps1 : ArraySeq[MapArea]) {
    val maps = maps1.sortBy(_.addr)
    val starts = maps.map(_.addr.low).toSeq

    println(maps.head)
    println(maps.last)

    for (a <- maps.map(_.addr).sliding(2))
        assert(a(0).high + Long.MinValue <= a(1).low + Long.MinValue)

    def findArea(addr: Long): Option[MapArea] = {
        val i = starts.search(addr).insertionPoint
        if (starts(i) == addr)
            Option(maps(i)) // special case: Found exact
        else if (i > 0)
            Option(maps(i-1)).filter(addr + Long.MinValue < _.addr.high + Long.MinValue)
        else
            Option.empty
    }
}

object ProcMaps {
    def apply(pid: Int): ProcMaps = {
        val mapfile = new java.io.FileInputStream(f"/proc/$pid%d/maps")
        val ls = lines(mapfile.readAllBytes())
        mapfile.close()
        new ProcMaps(ArraySeq.from(ls.map(MapArea.apply)))
    }
}

trait RandomAccess {
    /// Returns an array starting at logical 'offs' of at most 'maxlen' bytes
    /// Returns empty array at EOF, returns nothing past EOF
    def read(offs: Long, maxlen: Int): Option[Array[Byte]]
}

object RandomAccess {
    implicit class AobRandomAccess(a: Array[Byte]) extends RandomAccess {
        def read(offs: Long, maxlen: Int): Option[Array[Byte]] = Option.when(offs <= a.length)(a.drop(offs.toInt).take(maxlen))
    }
}


class ForeignMemory(val pid: Int, val maps: ProcMaps) extends RandomAccess {
    private val memFile = f"/proc/$pid%d/mem"
    private val reader = new RandomAccessFile(memFile, "r")
    private def shouldRead(map: MapArea): Boolean = {
        map.flags.readable && !map.flags.executable && !(map.path.map(_.startsWith("[v")).getOrElse(false))
    }
    private def read(addr: Long, len: Long): Array[Byte] = {
        assert(len < Int.MaxValue)
        //println(maps.findArea(addr))
        val arr = new Array[Byte](len.toInt)
        reader.seek(addr)
        reader.readFully(arr)
        arr
    }
    val snapshot = maps.maps.filter(shouldRead).map(a => (a.addr.low, read(a.addr.low, a.addr.length))).toMap
    reader.close()
    def getArea(addr: Long): Option[(MapArea, Array[Byte], Long)] = {
        maps.findArea(addr).flatMap(a => snapshot.get(a.addr.low).map((a, _, addr - a.addr.low)))
    }
    def read(offs: Long, maxlen: Int): Option[Array[Byte]] = getArea(offs).filter{case (m, _, o) => o < m.addr.length}.map{case (_, a, o) => a.drop(o.toInt).take(maxlen)}
}

object ForeignMemory {
    def apply(pid: Int): ForeignMemory = {
        new ForeignMemory(pid, ProcMaps(pid))
    }
}

private object Helper {
    def splitByLim[T](x: Array[T], c: T, lim: Int): (List[Array[T]], Array[T]) = {
        val idxs = x.zipWithIndex
            .filter(_._1 == c)
            .map(_._2 + 1)
            .appended(x.length+1)
            .take(lim)
        val list = idxs
            .prepended(0)
            .sliding(2)
            .map(a => x.slice(a(0), a(1)-1))
            .toList
        (list, x.slice(idxs.last, x.length))
    }
    def splitBy[T](x: Array[T], c: T): (List[Array[T]], Array[T]) = {
        val idxs = x.zipWithIndex
            .filter(_._1 == c)
            .map(_._2 + 1)
        val list = idxs
            .prepended(0)
            .sliding(2)
            .map(a => x.slice(a(0), a(1)-1))
            .toList
        (list, x.slice(idxs.last, x.length))
    }
    def splitBy2[T](x: Array[T], c: T): List[Array[T]] = {
        val (list, rest) = splitBy(x, c)
        list.appended(rest)
    }
    def lines(x: Array[Byte]): List[Array[Byte]] = {
        val (list, rest) = splitBy[Byte](x, '\n')
        assert(rest.length == 0)
        list
    }
    def parseHexInt(b: Array[Byte]): Long = {
        HexFormat.fromHexDigitsToLong(SeqCharSequence(b.map(_.toChar)))
    }
    def parseLong(b: Array[Byte], radix: Int): Long = {
        java.lang.Long.parseUnsignedLong(SeqCharSequence(b.map(_.toChar)), 0, b.length, radix)
    }

    def b2s(b:Array[Byte]): String = String.valueOf(b.map(_.toChar))
    def s2b(s:String): Array[Byte] = s.map(_.toByte).toArray
}