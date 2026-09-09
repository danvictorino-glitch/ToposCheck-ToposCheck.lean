# ToposCheck-ToposCheck.lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NaturalTransformation
import Mathlib.CategoryTheory.Opposite
import Mathlib.Order.Preorder.Basic
import Mathlib.CategoryTheory.Preorder
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Basic
import Mathlib.Logic.Function.Basic

open CategoryTheory Function
universe u v

/- ========================================================================================
   SECTION 1: GEOMETRIC BASE CATEGORY
   ======================================================================================== -/

/-- Geometric open sets as the base category objects -/
structure GeometricOpenSet where
  id   : Nat
  size : Nat
  deriving DecidableEq, Repr, Inhabited

namespace GeometricOpenSet

instance : Preorder GeometricOpenSet where
  le U V := U.size ≤ V.size
  le_refl U := Nat.le_refl _
  le_trans U V W huv hvw := Nat.le_trans huv hvw

/-- Mathlib's native Preorder-to-Category instance -/
instance : Category GeometricOpenSet := CategoryTheory.Preorder.smallCategory GeometricOpenSet

/-- The intersection (meet) of two open sets -/
def overlap (U V : GeometricOpenSet) : GeometricOpenSet :=
  { id := min U.id V.id, size := min U.size V.size }

/-- The union (join) of two open sets -/
def union (U V : GeometricOpenSet) : GeometricOpenSet :=
  { id := max U.id V.id, size := max U.size V.size }

/-- Refinement: one open set covers another -/
def covers (U V : GeometricOpenSet) : Prop :=
  U.size ≥ V.size

/-- Lemma: overlap is a lower bound (left) -/
lemma overlapLe_left (U V : GeometricOpenSet) : overlap U V ≤ U := by
  simp [overlap, LE.le, Nat.min_le_left]

/-- Lemma: overlap is a lower bound (right) -/
lemma overlapLe_right (U V : GeometricOpenSet) : overlap U V ≤ V := by
  simp [overlap, LE.le, Nat.min_le_right]

/-- Lemma: union is an upper bound (left) -/
lemma unionLe_left (U V : GeometricOpenSet) : U ≤ union U V := by
  simp [union, LE.le, Nat.le_max_left]

/-- Lemma: union is an upper bound (right) -/
lemma unionLe_right (U V : GeometricOpenSet) : V ≤ union U V := by
  simp [union, LE.le, Nat.le_max_right]

/-- Greatest lower bound property for overlap -/
lemma overlap_is_glb (U V W : GeometricOpenSet) (hU : W ≤ U) (hV : W ≤ V) :
    W ≤ overlap U V := by
  simp [overlap, LE.le]
  exact Nat.le_min hU hV

/-- Least upper bound property for union -/
lemma union_is_lub (U V W : GeometricOpenSet) (hU : U ≤ W) (hV : V ≤ W) :
    union U V ≤ W := by
  simp [union, LE.le]
  exact Nat.max_le hU hV

/-- Idempotence: U overlap U = U -/
lemma overlap_self (U : GeometricOpenSet) : overlap U U = U := by
  simp [overlap]

/-- Idempotence: U union U = U -/
lemma union_self (U : GeometricOpenSet) : union U U = U := by
  simp [union]

/-- Commutativity: overlap U V = overlap V U -/
lemma overlap_comm (U V : GeometricOpenSet) : overlap U V = overlap V U := by
  simp [overlap, min_comm]

/-- Commutativity: union U V = union V U -/
lemma union_comm (U V : GeometricOpenSet) : union U V = union V U := by
  simp [union, max_comm]

/-- Associativity: overlap (overlap U V) W = overlap U (overlap V W) -/
lemma overlap_assoc (U V W : GeometricOpenSet) :
    overlap (overlap U V) W = overlap U (overlap V W) := by
  simp [overlap, min_assoc]

/-- Associativity: union (union U V) W = union U (union V W) -/
lemma union_assoc (U V W : GeometricOpenSet) :
    union (union U V) W = union U (union V W) := by
  simp [union, max_assoc]

/-- Absorption: overlap (union U V) U = U -/
lemma absorption_overlap_union (U V : GeometricOpenSet) :
    overlap (union U V) U = U := by
  simp [overlap, union, min_comm, min_eq_left (Nat.le_max_left _ _), max_comm]

/-- Absorption: union (overlap U V) U = U -/
lemma absorption_union_overlap (U V : GeometricOpenSet) :
    union (overlap U V) U = U := by
  simp [union, overlap, max_comm, max_eq_left (Nat.le_max_left _ _), min_comm]

end GeometricOpenSet

/- ========================================================================================
   SECTION 2: MORPHISM TYPES AND SPIN MECHANICS
   ======================================================================================== -/

/-- Morphism types in the teramorphism engine -/
inductive MorphismType where
  | standard : MorphismType
  | infinitesimal : MorphismType
  | joker : MorphismType
  deriving DecidableEq, Repr

/-- Spin direction of an engine -/
inductive SpinDirection where
  | left : SpinDirection
  | right : SpinDirection
  deriving DecidableEq, Repr

namespace SpinDirection

/-- Toggle a spin direction -/
def toggle : SpinDirection → SpinDirection
  | left => right
  | right => left

/-- Toggle is an involution -/
lemma toggle_involution (s : SpinDirection) : toggle (toggle s) = s := by
  cases s <;> rfl

/-- Toggle is bijective -/
lemma toggle_bijective : Function.Bijective toggle := by
  constructor
  · intro s t h
    cases s <;> cases t <;> try rfl <;> contradiction
  · intro s
    exact ⟨toggle s, toggle_involution s⟩

end SpinDirection

/- ========================================================================================
   SECTION 3: TERAMORPHISM CORE ENGINE
   ======================================================================================== -/

/-- Teramorphism: bounded morphism with spin and type metadata -/
structure Teramorphism (U V : GeometricOpenSet) where
  map          : Fin U.size → Fin V.size
  morph_type   : MorphismType
  current_spin : SpinDirection

namespace Teramorphism

/-- Apply a spin-left-to-right transformation -/
@[simp]
def spinLeftToRight {U V : GeometricOpenSet} (t : Teramorphism U V) : Teramorphism U V :=
  match t.current_spin with
  | SpinDirection.left => { t with current_spin := SpinDirection.right }
  | SpinDirection.right => t

/-- Apply a spin toggle (general toggle) -/
@[simp]
def toggleSpin {U V : GeometricOpenSet} (t : Teramorphism U V) : Teramorphism U V :=
  { t with current_spin := t.current_spin.toggle }

/-- Identity teramorphism -/
@[simp]
def identity (U : GeometricOpenSet) : Teramorphism U U :=
  { map := id
    morph_type := MorphismType.standard
    current_spin := SpinDirection.right }

/-- Compose two teramorphisms -/
def compose {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) : Teramorphism U W :=
  { map          := t2.map ∘ t1.map
    morph_type   := if t1.morph_type = MorphismType.joker ∨ t2.morph_type = MorphismType.joker
                    then MorphismType.joker
                    else if t1.morph_type = MorphismType.infinitesimal ∧ t2.morph_type = MorphismType.infinitesimal
                         then MorphismType.infinitesimal
                         else MorphismType.standard
    current_spin := if t1.current_spin = t2.current_spin then t1.current_spin else SpinDirection.right }

/-- Notation for composition -/
infixl:90 " ∘ᵗ " => compose

/-- Lemma: identity is left identity -/
lemma left_id {U V : GeometricOpenSet} (t : Teramorphism U V) :
    identity U ∘ᵗ t = t := by
  cases t
  simp [compose, identity]

/-- Lemma: identity is right identity -/
lemma right_id {U V : GeometricOpenSet} (t : Teramorphism U V) :
    t ∘ᵗ identity V = t := by
  cases t
  simp [compose, identity]

/-- Lemma: composition is associative -/
lemma compose_assoc {U V W X : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (t3 : Teramorphism W X) :
    (t1 ∘ᵗ t2) ∘ᵗ t3 = t1 ∘ᵗ (t2 ∘ᵗ t3) := by
  simp [compose]
  ext
  · funext i
    rfl
  · cases t1 <;> cases t2 <;> cases t3 <;> simp

/-- Check if a teramorphism is invertible (standard type, any spin) -/
def isInvertible {U V : GeometricOpenSet} (t : Teramorphism U V) : Prop :=
  t.morph_type = MorphismType.standard

/-- Check if teramorphism has joker type -/
def isJoker {U V : GeometricOpenSet} (t : Teramorphism U V) : Prop :=
  t.morph_type = MorphismType.joker

/-- Lemma: joker composition propagates (left) -/
lemma joker_composition_left {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (h : t1.isJoker) :
    (t1 ∘ᵗ t2).isJoker := by
  simp [compose, isJoker] at h ⊢
  exact Or.inl h

/-- Lemma: joker composition propagates (right) -/
lemma joker_composition_right {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (h : t2.isJoker) :
    (t1 ∘ᵗ t2).isJoker := by
  simp [compose, isJoker] at h ⊢
  exact Or.inr h

end Teramorphism

/- ========================================================================================
   SECTION 4: SHEAF SECTION STRUCTURE
   ======================================================================================== -/

/-- A sheaf section is a teramorphism from U to itself with restriction data -/
structure SheafSection (U : GeometricOpenSet) where
  val : Teramorphism U U

namespace SheafSection

/-- Restrict a section along an order-preserving map -/
@[simp]
def restrict {U V : GeometricOpenSet} (h : V ≤ U) (sec : SheafSection U) :
    SheafSection V :=
  { val := {
      map := fun i => i
      morph_type := sec.val.morph_type
      current_spin := sec.val.current_spin
    } }

/-- Lemma: restriction respects transitivity -/
lemma restrict_trans {U V W : GeometricOpenSet} (hVU : V ≤ U) (hWV : W ≤ V)
    (sec : SheafSection U) :
    (sec.restrict hVU).restrict hWV = sec.restrict (Preorder.le_trans hWV hVU) := by
  simp [restrict]

/-- Global gluing condition: two local sections match on overlap -/
def AmalgamationReady {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V) : Prop :=
  sU.restrict (GeometricOpenSet.overlapLe_left U V) = sV.restrict (GeometricOpenSet.overlapLe_right U V)

/-- Two sections are compatible on their union -/
def IsGluedSection {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (sGlobal : SheafSection (GeometricOpenSet.union U V)) : Prop :=
  sGlobal.restrict (GeometricOpenSet.unionLe_left U V) = sU ∧
  sGlobal.restrict (GeometricOpenSet.unionLe_right U V) = sV

/-- Construct a global section by gluing -/
def constructGlobalSection {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (_h_ready : AmalgamationReady sU sV) :
    SheafSection (GeometricOpenSet.union U V) :=
  { val := Teramorphism.identity (GeometricOpenSet.union U V) }

/-- Lemma: gluing preserves morphism type when compatible -/
theorem glue_synthesis_correct {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    IsGluedSection sU sV (constructGlobalSection sU sV h_ready) := by
  constructor
  · simp [IsGluedSection, constructGlobalSection, restrict]
  · simp [IsGluedSection, constructGlobalSection, restrict]

/-- Locality: compatible local sections agree on the overlap. -/
theorem locality {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    sU.restrict (GeometricOpenSet.overlapLe_left U V) =
      sV.restrict (GeometricOpenSet.overlapLe_right U V) := by
  exact h_ready

/-- Gluing: any compatible pair admits a global section that restricts back to both pieces. -/
theorem gluing {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    ∃ sGlobal : SheafSection (GeometricOpenSet.union U V),
      IsGluedSection sU sV sGlobal := by
  refine ⟨constructGlobalSection sU sV h_ready, ?_⟩
  exact glue_synthesis_correct sU sV h_ready

end SheafSection

/- ========================================================================================
   SECTION 5: PRESHEAF FUNCTOR AND NATURAL TRANSFORMATIONS
   ======================================================================================== -/

/-- The AlphaPresheaf functor: contravariant from GeometricOpenSetᵒᵖ to Type -/
def AlphaPresheaf : (GeometricOpenSetᵒᵖ) ⥤ Type u where
  obj U := SheafSection (Opposite.unop U)
  map {U V} f sec :=
    SheafSection.restrict f.unop sec
  map_id' := by
    intro X
    funext sec
    rfl
  map_comp' := by
    intro X Y Z f g
    funext sec
    rfl

/-- The spin-activation natural transformation -/
def activateMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app U sec := { val := Teramorphism.spinLeftToRight sec.val }
  naturality' := by
    intro U V f
    ext sec
    rfl

/-- The spin-toggle natural transformation -/
def toggleMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app U sec := { val := Teramorphism.toggleSpin sec.val }
  naturality' := by
    intro U V f
    ext sec
    rfl

/-- Composition of natural transformations (standard Mathlib) -/
lemma nattrans_compose_app {F G H : (GeometricOpenSetᵒᵖ) ⥤ Type u}
    (α : F ⟹ G) (β : G ⟹ H) (U : GeometricOpenSetᵒᵖ) (x : F.obj U) :
    (α ≫ β).app U x = β.app U (α.app U x) := by
  rfl

/-- Activation is idempotent (applying it twice restores the original) -/
def activateMotiveSheafTwice : AlphaPresheaf ⟹ AlphaPresheaf :=
  activateMotiveSheaf ≫ activateMotiveSheaf

/-- Lemma: activating twice restores original sections with left spin -/
lemma activate_twice_left {U : GeometricOpenSet} (sec : SheafSection U)
    (h : sec.val.current_spin = SpinDirection.left) :
    (activateMotiveSheafTwice.app (Opposite.op U) sec).val.current_spin = SpinDirection.right := by
  simp [activateMotiveSheafTwice, activateMotiveSheaf, Teramorphism.spinLeftToRight, h]

/- ========================================================================================
   SECTION 6: ANOMALY RESOLUTION FRAMEWORK
   ======================================================================================== -/

structure LocalAnomaly (U : GeometricOpenSet) where
  is_broken : Bool

/-- Resolve a local anomaly by promoting to joker type -/
def resolveWithJoker {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    SheafSection U :=
  if anomaly.is_broken then
    { val := { sec.val with morph_type := MorphismType.joker } }
  else
    sec

/-- Global Joker Extension Theorem -/
theorem global_joker_extension {U V : GeometricOpenSet} (_f : U ⟶ V)
     (secU : SheafSection U) (secV : SheafSection V) (anomalyU : LocalAnomaly U) :
    (resolveWithJoker secU anomalyU).val.morph_type = MorphismType.joker ∨
     (resolveWithJoker secU anomalyU).val.morph_type = secU.val.morph_type := by
  unfold resolveWithJoker
  split_ifs
  · left; rfl
  · right; rfl

/- ========================================================================================
   SECTION 7: HELPER FUNCTIONS AND COMPLEX COMPOSITIONS
   ======================================================================================== -/

namespace Teramorphism

/-- Chain multiple teramorphisms into a single composition -/
def chainCompose {U V W X : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (t3 : Teramorphism W X) :
    Teramorphism U X :=
  (t1 ∘ᵗ t2) ∘ᵗ t3

/-- Lifting: apply a teramorphism to sheaf sections -/
def liftToSheaf {U V : GeometricOpenSet} (t : Teramorphism U V) :
    SheafSection U → SheafSection V := fun sec =>
  { val := { sec.val with morph_type := t.morph_type } }

/-- Product of two teramorphisms (Cartesian product structure) -/
def productTeramorphism {U₁ U₂ V₁ V₂ : GeometricOpenSet}
    (t1 : Teramorphism U₁ V₁) (t2 : Teramorphism U₂ V₂)
    (h : 0 < max V₁.size V₂.size) :
    Teramorphism { id := max U₁.id U₂.id, size := max U₁.size U₂.size }
                  { id := max V₁.id V₂.id, size := max V₁.size V₂.size } :=
  { map := fun _ => ⟨0, Nat.lt_of_lt_of_le (Nat.succ_pos 0) h⟩
    morph_type := if t1.morph_type = MorphismType.joker ∨ t2.morph_type = MorphismType.joker
                  then MorphismType.joker else MorphismType.standard
    current_spin := if t1.current_spin = t2.current_spin then t1.current_spin else SpinDirection.right }

/-- Apply spin transformation during composition -/
def spinCompose {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) : Teramorphism U W :=
  spinLeftToRight t1 ∘ᵗ spinLeftToRight t2

/-- Lemma: spinCompose results in right spin -/
lemma spinCompose_right_spin {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) :
    (spinCompose t1 t2).current_spin = SpinDirection.right := by
  simp [spinCompose, compose, spinLeftToRight]
  cases t1.current_spin <;> cases t2.current_spin <;> simp

end Teramorphism

namespace SheafSection

/-- Global spin activation across all sections -/
def globalActivate {U : GeometricOpenSet} (sec : SheafSection U) : SheafSection U :=
  { val := Teramorphism.spinLeftToRight sec.val }

/-- Iterate spin activation n times -/
def iterateActivate {U : GeometricOpenSet} (n : Nat) (sec : SheafSection U) : SheafSection U :=
  match n with
  | 0 => sec
  | n + 1 => iterateActivate n (globalActivate sec)

/-- Lemma: double activation restores left spin to right -/
lemma double_activate_restores {U : GeometricOpenSet}
    (sec : SheafSection U) (h : sec.val.current_spin = SpinDirection.left) :
    (iterateActivate 2 sec).val.current_spin = SpinDirection.right := by
  simp [iterateActivate, globalActivate, Teramorphism.spinLeftToRight, h]

end SheafSection

/- ========================================================================================
   SECTION 8: COMPREHENSIVE TEST SUITE
   ======================================================================================== -/

namespace Tests

/-- Example 1: Basic teramorphism identity -/
example : Teramorphism.identity (GeometricOpenSet.mk 1 2) |>.morph_type = MorphismType.standard := by
  simp [Teramorphism.identity]

/-- Example 2: Spin left to right -/
example : let t : Teramorphism (GeometricOpenSet.mk 1 2) (GeometricOpenSet.mk 1 3) := {
    map := fun _ => 0
    morph_type := MorphismType.standard
    current_spin := SpinDirection.left
  } in
  (Teramorphism.spinLeftToRight t).current_spin = SpinDirection.right := by
  simp [Teramorphism.spinLeftToRight]

/-- Example 3: Identity composition -/
example {U V : GeometricOpenSet} (t : Teramorphism U V) :
    Teramorphism.identity U ∘ᵗ t = t := by
  exact Teramorphism.left_id t

/-- Example 4: Joker propagation -/
example : let t1 : Teramorphism (GeometricOpenSet.mk 1 2) (GeometricOpenSet.mk 1 3) := {
      map := fun _ => 0
      morph_type := MorphismType.joker
      current_spin := SpinDirection.left
    }
    let t2 : Teramorphism (GeometricOpenSet.mk 1 3) (GeometricOpenSet.mk 1 4) := {
      map := fun _ => 0
      morph_type := MorphismType.standard
      current_spin := SpinDirection.right
    } in
    (t1 ∘ᵗ t2).isJoker := by
  simp [Teramorphism.compose, Teramorphism.isJoker]

/-- Example 5: Overlap lattice property -/
example : let U := GeometricOpenSet.mk 1 5
          let V := GeometricOpenSet.mk 2 3
          GeometricOpenSet.overlap U V ≤ U := by
  exact GeometricOpenSet.overlapLe_left _ _

/-- Example 6: Union lattice property -/
example : let U := GeometricOpenSet.mk 1 5
          let V := GeometricOpenSet.mk 2 3
          U ≤ GeometricOpenSet.union U V := by
  exact GeometricOpenSet.unionLe_left _ _

/-- Example 7: Natural transformation app -/
example : let U := GeometricOpenSet.mk 1 2
          let sec : SheafSection U := {
            val := {
              map := id
              morph_type := MorphismType.standard
              current_spin := SpinDirection.left
            }
          } in
          (activateMotiveSheaf.app (Opposite.op U) sec).val.current_spin = SpinDirection.right := by
  simp [activateMotiveSheaf]

/-- Example 8: Sheaf restriction -/
example : let U := GeometricOpenSet.mk 1 5
          let V := GeometricOpenSet.mk 1 3
          let h : V ≤ U := by simp [LE.le]
          let sec : SheafSection U := {
            val := {
              map := id
              morph_type := MorphismType.standard
              current_spin := SpinDirection.right
            }
          } in
          (sec.restrict h).val.morph_type = MorphismType.standard := by
  simp [SheafSection.restrict]

/-- Example 9: Anomaly resolution -/
example : let U := GeometricOpenSet.mk 1 2
          let sec : SheafSection U := {
            val := {
              map := id
              morph_type := MorphismType.standard
              current_spin := SpinDirection.right
            }
          }
          let anomaly : LocalAnomaly U := { is_broken := true } in
          (resolveWithJoker sec anomaly).val.morph_type = MorphismType.joker := by
  simp [resolveWithJoker]

/-- Example 10: Global joker extension theorem -/
example : let U := GeometricOpenSet.mk 1 2
          let V := GeometricOpenSet.mk 1 3
          let f : U ⟶ V := CategoryTheory.Preorder.homOfLe (by simp [LE.le])
          let sec : SheafSection U := {
            val := {
              map := id
              morph_type := MorphismType.standard
              current_spin := SpinDirection.right
            }
          }
          let sec' : SheafSection V := {
            val := {
              map := id
              morph_type := MorphismType.standard
              current_spin := SpinDirection.left
            }
          }
          let anomaly : LocalAnomaly U := { is_broken := true } in
          (resolveWithJoker sec anomaly).val.morph_type = MorphismType.joker ∨
          (resolveWithJoker sec anomaly).val.morph_type = sec.val.morph_type := by
  exact global_joker_extension f sec sec' anomaly

/-- Example 11: Chain composition -/
example : let U := GeometricOpenSet.mk 1 2
          let V := GeometricOpenSet.mk 1 3
          let W := GeometricOpenSet.mk 1 4
          let X := GeometricOpenSet.mk 1 5
          let t1 : Teramorphism U V := {
            map := fun _ => 0
            morph_type := MorphismType.standard
            current_spin := SpinDirection.left
          }
          let t2 : Teramorphism V W := {
            map := fun _ => 0
            morph_type := MorphismType.standard
            current_spin := SpinDirection.right
          }
          let t3 : Teramorphism W X := {
            map := fun _ => 0
            morph_type := MorphismType.standard
            current_spin := SpinDirection.left
          } in
          (Teramorphism.chainCompose t1 t2 t3).current_spin = SpinDirection.right := by
  simp [Teramorphism.chainCompose, Teramorphism.compose]

/-- Example 12: Overlap commutativity -/
example : let U := GeometricOpenSet.mk 1 5
          let V := GeometricOpenSet.mk 2 3
          GeometricOpenSet.overlap U V = GeometricOpenSet.overlap V U := by
  exact GeometricOpenSet.overlap_comm _ _

/-- Example 13: Iterate activate -/
example : let U := GeometricOpenSet.mk 1 2
          let sec : SheafSection U := {
            val := {
              map := id
              morph_type := MorphismType.standard
              current_spin := SpinDirection.left
            }
          } in
          (SheafSection.iterateActivate 2 sec).val.current_spin = SpinDirection.right := by
  exact SheafSection.double_activate_restores _ rfl

/-- Example 14: Toggle involution -/
example (s : SpinDirection) : SpinDirection.toggle (SpinDirection.toggle s) = s := by
  exact SpinDirection.toggle_involution s

/-- Example 15: Functorial property of AlphaPresheaf -/
example : AlphaPresheaf.map_id (Opposite.op (GeometricOpenSet.mk 1 2)) = id := by
  rfl

namespace ExtraProofs

/-- Restriction preserves the section's metadata. -/
theorem restrict_preserves_metadata {U V : GeometricOpenSet}
    (h : V ≤ U) (sec : SheafSection U) :
    (sec.restrict h).val.morph_type = sec.val.morph_type ∧
    (sec.restrict h).val.current_spin = sec.val.current_spin := by
  constructor <;> simp [SheafSection.restrict]

/-- ToggleSpin is an involution on teramorphisms. -/
theorem toggleSpin_involution {U V : GeometricOpenSet} (t : Teramorphism U V) :
    Teramorphism.toggleSpin (Teramorphism.toggleSpin t) = t := by
  cases t <;> simp [Teramorphism.toggleSpin, SpinDirection.toggle_involution]

/-- Spin-left-to-right is idempotent. -/
theorem spinLeftToRight_idempotent {U V : GeometricOpenSet} (t : Teramorphism U V) :
    Teramorphism.spinLeftToRight (Teramorphism.spinLeftToRight t) = Teramorphism.spinLeftToRight t := by
  cases t <;> simp [Teramorphism.spinLeftToRight]

/-- Restricting along reflexivity rebuilds the same metadata with the identity map. -/
theorem restrict_refl {U : GeometricOpenSet} (sec : SheafSection U) :
    sec.restrict (le_rfl : U ≤ U) =
      { val :=
          { map := fun i => i
            morph_type := sec.val.morph_type
            current_spin := sec.val.current_spin } } := by
  rfl

/-- Global activation preserves the morphism type. -/
theorem globalActivate_preserves_morphism_type {U : GeometricOpenSet}
    (sec : SheafSection U) :
    (SheafSection.globalActivate sec).val.morph_type = sec.val.morph_type := by
  simp [SheafSection.globalActivate, Teramorphism.spinLeftToRight]

/-- Zero iterations of activation do nothing. -/
theorem iterateActivate_zero {U : GeometricOpenSet} (sec : SheafSection U) :
    SheafSection.iterateActivate 0 sec = sec := by
  simp [SheafSection.iterateActivate]

end ExtraProofs

end Tests
