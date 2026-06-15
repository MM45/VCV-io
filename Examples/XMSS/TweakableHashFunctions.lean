universe up ut ux uy

abbrev TweakableHash (PP : Type up) (TW : Type ut) (X : Type ux) (Y : Type uy) :=
  PP → TW → X → Y

universe uα
def indexedIterate {α : Type uα}
    (f : Nat → α → α)
    (start : Nat) :
    Nat → α → α
  | 0, x => x
  | steps + 1, x => f (start + steps) (indexedIterate f start steps x)

theorem indexedIterate_comp {α : Type uα}
    (f : Nat → α → α)
    (start i j : Nat)
    (x : α) :
    indexedIterate f start (i + j) x
    =
    indexedIterate f (start + i) j (indexedIterate f start i x) :=
  by
  induction j with
  | zero =>
      simp [indexedIterate]
  | succ j ih =>
      simp [indexedIterate, ih, Nat.add_assoc]

namespace TweakableHash

def chain {PP : Type up} {TW : Type ut} {X : Type ux} {Y : Type uy}
    (outToIn : Y → X)
    (thf : TweakableHash PP TW X Y)
    (twat : Nat → TW)
    (pp : PP)
    (start steps : Nat)
    (x : Y) : Y :=
  indexedIterate
    (fun pos y => thf pp (twat pos) (outToIn y))
    start
    steps
    x

theorem chain_comp {PP : Type up} {TW : Type ut} {X : Type ux} {Y : Type uy}
    (outToIn : Y → X)
    (thf : TweakableHash PP TW X Y)
    (twat : Nat → TW)
    (pp : PP)
    (start i j : Nat)
    (x : Y) :
    chain outToIn thf twat pp start (i + j) x
    =
    chain outToIn thf twat pp (start + i) j (chain outToIn thf twat pp start i x) :=
  by
  simp [chain, indexedIterate_comp]

end TweakableHash
