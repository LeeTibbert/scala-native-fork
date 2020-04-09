package scala.scalanative
package nscplugin

trait NirGenUtil { self: NirGenPhase =>
  import global._

  def genParamSyms(dd: DefDef, isStatic: Boolean): Seq[Option[Symbol]] = {
    val vp     = dd.vparamss
    val params = if (vp.isEmpty) Nil else vp.head.map(p => Some(p.symbol))
    if (isStatic) params else None +: params
  }
}
