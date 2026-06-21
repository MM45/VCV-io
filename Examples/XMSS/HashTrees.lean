universe u

inductive HashTree (H : Type u) where
  | leaf (value : H)
  | node (value : H) (left right : HashTree H)

namespace HashTree

variable {H : Type u}

def value : HashTree H → H
  | .leaf value => value
  | .node value _ _ => value

def height : HashTree H → Nat
  | .leaf _ => 0
  | .node _ l r => 1 + max (height l) (height r)

def numLeaves : HashTree H → Nat
  | .leaf _ => 1
  | .node _ l r => l.numLeaves + r.numLeaves



def IsPerfect : HashTree H → Prop
  | .leaf _ => True
  | .node _ l r => l.height = r.height ∧ l.IsPerfect ∧ r.IsPerfect

def IsBalanced : HashTree H → Prop
  | .leaf _ => True
  | .node _ l r => (l.height - r.height) + (r.height - l.height) ≤ 1

def IsPerfectlyBalanced : HashTree H → Prop
  | .leaf _ => True
  | .node _ l r => l.height = r.height

/- def fromLeaves
 -     (leaves : List H)
 -     (f : Nat → Nat → H → H → H)
 -     (idx : Nat × Nat) : HashTree H :=
 -   f idx₁ idx₂
 -     (fromLeaves (firstHalf leaves) f (idx₁ + 1, 2 * idx₂))
 -     (fromLeaves (secondHalf leaves) f (idx₁ + 1, 2 * idx₁ + 1)) -/

end HashTree
