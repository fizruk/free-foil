import Foil.DExt
import scala.collection.immutable.IntMap

object Foil extends App {

  sealed trait Expr[N <: S]

  case class VarE[N <: S](name: Name[N])                                   extends Expr[N]
  case class AppE[N <: S](fun: Expr[N], arg: Expr[N])                      extends Expr[N]
  case class LamE[N <: S, L <: S](binder: NameBinder[N, L], body: Expr[L]) extends Expr[N]

  case class RawName(rawId: Int)

  case class RawScope(rawSet: Set[Int])

  val rawEmptyScope: RawScope = RawScope(Set.empty[Int])

  def rawFreshName(rawScope: RawScope): RawName = rawScope match {
    case RawScope(s) if s.isEmpty => RawName(0)
    case RawScope(s)              => RawName(s.max + 1)
  }

  def rawExtendScope(rawName: RawName, rawScope: RawScope): RawScope =
    RawScope(rawScope.rawSet + rawName.rawId)

  def rawMember(rawName: RawName)(rawScope: RawScope): Boolean =
    rawScope.rawSet.contains(rawName.rawId)

  case class RawSubst[A](rawMap: IntMap[A])

  def rawIdSubst[A] = IntMap.empty[A]

  def rawLookup[A](rawSubst: RawSubst[A])(rawName: RawName): Option[A] =
    rawSubst.rawMap.get(rawName.rawId)

  def rawExtendSubst[A](rawName: RawName, value: A, rawSubst: RawSubst[A]): RawSubst[A] =
    RawSubst(rawSubst.rawMap.updated(rawName.rawId, value))

  sealed trait S
  case class VoidS() extends S

  case class Name[N <: S](unsafeName: RawName)
  case class Scope[N <: S](unsafeScope: RawScope)

  val emptyScope = Scope[VoidS](rawEmptyScope)

  def member[L <: S, N <: S](name: Name[L])(scope: Scope[N]): Boolean =
    rawMember(name.unsafeName)(scope.unsafeScope)

  case class NameBinder[N <: S, L <: S](unsafeBinder: Name[L])

  def nameOf[N <: S, L <: S](nameBinder: NameBinder[N, L]): Name[L] =
    nameBinder.unsafeBinder

  def withFreshBinder[N <: S, R](scope: Scope[N])(cont: [L <: S] => NameBinder[N, L] => R): R =
    cont(NameBinder(Name(rawFreshName(scope.unsafeScope))))

  class Distinct[N <: S]
  class ExtEndo[N <: S]
  class Ext[N <: S, L <: S](implicit ev: ExtEndo[N] <:< ExtEndo[L])

  type DExt[N <: S, L <: S] = (Distinct[L], Ext[N, L])

  sealed trait DistinctEvidence[N <: S]
  case object Distinct extends DistinctEvidence[VoidS]
  val unsafeDistinct: DistinctEvidence[VoidS] = Distinct

  sealed trait ExtEvidence[N <: S, L <: S]
  case object Ext extends ExtEvidence[VoidS, VoidS]
  val unsafeExt: ExtEvidence[VoidS, VoidS] = Ext

  class Sinkable[E[_ <: S]] {
    def sinkabilityProof[N <: S, L <: S](rename: Name[N] => Name[L]): E[N] => E[L] = ???
  }

  object Sinkable {
    given nameSinkable: Sinkable[Name] = new Sinkable[Name]
    given exprSinkable: Sinkable[Expr] = new Sinkable[Expr]
    given substitutionSinkable[E[_ <: S], I <: S](
        using sinkable: Sinkable[E],
    ): Sinkable[[O <: S] =>> Substitution[E, I, O]] with {
      def sinkabilityProof[N <: S, L <: S](
          rename: Name[N] => Name[L],
          substitution: Substitution[E, I, N],
      ): Substitution[E, I, L] = ???
    }
  }

  def sink[E[_ <: S]: Sinkable, N <: S, L <: S](en: E[N])(using ev: DExt[N, L]): E[L] = en.asInstanceOf[E[L]]

  def unsafeAssertFresh[N <: S, L <: S, N1 <: S, L1 <: S, R](
      binder: NameBinder[N, L],
  )(cont: DExt[N1, L1] ?=> NameBinder[N1, L1] => R): R = {
    given DExt[N1, L1] = (unsafeDistinct.asInstanceOf[Distinct[L1]], unsafeExt.asInstanceOf[Ext[N1, L1]])
    cont(binder.asInstanceOf[NameBinder[N1, L1]])
  }

  def withFresh[N <: S: Distinct, R](scope: Scope[N])(cont: [L <: S] => DExt[N, L] ?=> NameBinder[N, L] => R): R = {
    withFreshBinder[N, R](scope)([L <: S] => (binder: NameBinder[N, L]) => unsafeAssertFresh(binder)(cont[L]))
  }

  def withRefreshed[O <: S, I <: S, R](scope: Scope[O], name: Name[I])(
      cont: [O1 <: S] => DExt[O, O1] ?=> NameBinder[O, O1] => R,
  ): R = {

    given Distinct[O] = unsafeDistinct.asInstanceOf[Distinct[O]]
    given DExt[O, O]  = (unsafeDistinct.asInstanceOf[Distinct[O]], unsafeExt.asInstanceOf[Ext[O, O]])
    if (member(name)(scope))
      withFresh(scope)(cont)
    else
      unsafeAssertFresh[O, I, O, I, R](NameBinder[O, I](name))(cont[I])
  }

  def extendScope[N <: S, L <: S](nameBinder: NameBinder[N, L], scope: Scope[N]): Scope[L] =
    Scope[L](rawExtendScope(nameBinder.unsafeBinder.unsafeName, scope.unsafeScope))

  case class Substitution[E[_ <: S], I <: S, O <: S](f: [N <: S] => Name[N] => E[N], env: IntMap[E[O]])

  def lookupSubst[E[_ <: S], I <: S, O <: S](subst: Substitution[E, I, O], name: Name[I]): E[O] =
    subst.env.get(name.unsafeName.rawId) match {
      case Some(e) => e
      case None    => subst.f(Name(RawName(name.unsafeName.rawId)))
    }

  def idSubst[E[_ <: S], I <: S](f: [N <: S] => Name[N] => E[N]): Substitution[E, I, I] =
    Substitution(f, IntMap.empty)

  def addSubst[E[_ <: S], I <: S, O <: S, I1 <: S](
      s: Substitution[E, I, O],
  )(b: NameBinder[I, I1])(e: E[O]): Substitution[E, I1, O] = s match {
    case Substitution(f, env) => Substitution(f, env)
  }

  def addRename[E[_ <: S], I <: S, I1 <: S, O <: S](
      s: Substitution[E, I, O],
      b: NameBinder[I, I1],
      n: Name[O],
  ): Substitution[E, I1, O] = (s, b, n) match {
    case (Substitution(f, env), NameBinder(Name(name1)), Name(name2)) =>
      if (name1 == name2)
        Substitution(f, env)
      else
        addSubst(s)(b)(f(n))
  }

  def substitute[O <: S, I <: S](scope: Scope[O], subst: Substitution[Expr, I, O], expr: Expr[I]): Expr[O] = expr match {
    case VarE(name) => lookupSubst(subst, name)
    case AppE(f, x) => AppE(substitute(scope, subst, f), substitute(scope, subst, x))
    case LamE(binder, body) => withRefreshed(scope, nameOf(binder))
      { [O1 <: S] => implicit dext: DExt[O, O1] => (binder_ : NameBinder[O, O1]) =>
      val subst_ = addRename(sink(subst), binder, nameOf(binder_))
      val scope_ = extendScope(binder_, scope)
      val body_ = substitute(scope_, subst_, body)
      LamE(binder_, body_)
    }
  }

}
