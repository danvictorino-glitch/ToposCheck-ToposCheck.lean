# ToposCheck-ToposCheck.lean
/-! # Fully Refined & Non-Trivial ToposCheck.lean (Corrected) -/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Homeomorph
import Mathlib.Order.CompleteLattice
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
open CategoryTheory Opposite

universe u v

/-! ## SECTION 0: AMBIENT SPACE -/
axiom AmbientSpace : Type u
axiom ambientTopology : TopologicalSpace AmbientSpace
noncomputable instance : TopologicalSpace AmbientSpace := ambientTopology

abbrev GeometricOpenSet := TopologicalSpace.Opens AmbientSpace

namespace GeometricOpenSet
def union (U V : GeometricOpenSet) : GeometricOpenSet := U ⊔ V
def overlap (U V : GeometricOpenSet) : GeometricOpenSet := U ⊓ V

@[simp] lemma union_comm (U V : GeometricOpenSet) : union U V = union V U := sup_comm U V
@[simp] lemma overlap_comm (U V : GeometricOpenSet) : overlap U V = overlap V U := inf_comm U V
lemma overlapLe_left (U V : GeometricOpenSet) : overlap U V ≤ U := inf_le_left
lemma overlapLe_right (U V : GeometricOpenSet) : overlap U V ≤ V := inf_le_right
lemma unionLe_left (U V : GeometricOpenSet) : U ≤ union U V := le_sup_left
lemma unionLe_right (U V : GeometricOpenSet) : V ≤ union U V := le_sup_right
end GeometricOpenSet

/-! ## SECTION 1: DYNAMIC MORPHISM TYPES & ALGEBRAIC SPIN -/
inductive MorphismType where
  | standard      : MorphismType
  | infinitesimal : MorphismType
  | joker         : MorphismType
  deriving DecidableEq, Repr

namespace MorphismType
def comp : MorphismType → MorphismType → MorphismType
  | joker, _ => joker
  | _, joker => joker
  | standard, standard => standard
  | _, _ => infinitesimal

instance : CommMonoid MorphismType where
  mul := comp
  one := standard
  mul_comm a b := by decide
  mul_assoc a b c := by decide
  one_mul a := by decide
  mul_one a := by decide

@[simp] lemma joker_absorbs (a : MorphismType) : joker * a = joker := rfl
end MorphismType

inductive SpinDirection where
  | left  : SpinDirection
  | right : SpinDirection
  deriving DecidableEq, Repr

namespace SpinDirection
def toggle : SpinDirection → SpinDirection
  | left => right
  | right => left

def toSign : SpinDirection → Int
  | left => 1
  | right => -1

instance : CommGroup SpinDirection where
  mul a b := match a, b with
    | left, left => left
    | left, right => right
    | right, left => right
    | right, right => left
  one := left
  inv a := a
  mul_assoc a b c := by decide
  mul_comm a b := by decide
  one_mul a := by decide
  mul_one a := by decide
  inv_mul_cancel a := by decide
end SpinDirection

/-! ## SECTION 2: TERAMORPHISM ENGINE -/
structure Teramorphism (U V : GeometricOpenSet) where
  map          : C(U, V)
  morph_type   : MorphismType
  current_spin : SpinDirection
  is_valid     : morph_type = MorphismType.standard → IsHomeomorphism map

namespace Teramorphism

@[simp] def identity (U : GeometricOpenSet) : Teramorphism U U :=
  { map := ContinuousMap.id U
    morph_type := MorphismType.standard
    current_spin := SpinDirection.left
    is_valid := fun _ => Homeomorph.isHomeomorphism (Homeomorph.refl U) }

def compose {U V W : GeometricOpenSet} (t1 : Teramorphism U V) (t2 : Teramorphism V W) : Teramorphism U W :=
  { map := t2.map.comp t1.map
    morph_type := t1.morph_type * t2.morph_type
    current_spin := t1.current_spin * t2.current_spin
    is_valid := by
      intro h
      have h1 : t1.morph_type = MorphismType.standard ∧ t2.morph_type = MorphismType.standard := by
        rcases t1.morph_type with _ | _ | _ <;> rcases t2.morph_type with _ | _ | _ <;> simp_all [HMul.hMul, Mul.mul, MorphismType.comp]
      exact IsHomeomorphism.comp (t2.is_valid h1.2) (t1.is_valid h1.1) }

infixl:90 " ∘ᵗ " => compose

lemma left_id {U V : GeometricOpenSet} (t : Teramorphism U V) : identity U ∘ᵗ t = t := by
  cases t; simp [compose, identity]

lemma right_id {U V : GeometricOpenSet} (t : Teramorphism U V) : t ∘ᵗ identity V = t := by
  cases t; simp [compose, identity]

lemma compose_assoc {U V W Y : GeometricOpenSet} (t1 : Teramorphism U V) (t2 : Teramorphism V W) (t3 : Teramorphism W Y) :
    (t1 ∘ᵗ t2) ∘ᵗ t3 = t1 ∘ᵗ (t2 ∘ᵗ t3) := by
  cases t1; cases t2; cases t3
  simp [compose, mul_assoc]

end Teramorphism

instance : Category GeometricOpenSet where
  Hom U V := Teramorphism U V
  id U := Teramorphism.identity U
  comp t1 t2 := t1 ∘ᵗ t2
  id_comp := Teramorphism.left_id
  comp_id := Teramorphism.right_id
  assoc := Teramorphism.compose_assoc

/-! ## SECTION 3: TWISTED SHEAF SECTIONS -/
structure SheafSection (U : GeometricOpenSet) where
  val         : Teramorphism U U
  phase_shift : Int

namespace SheafSection

noncomputable def restrictMap {U V : GeometricOpenSet} (h : V ≤ U) (f : C(U, U)) : C(V, V) where
  toFun x := ⟨(f ⟨x.1, h x.2⟩).1, (f ⟨x.1, h x.2⟩).2⟩
  continuous_toFun := by continuous_subtype_pullback

noncomputable def restrict {U V : GeometricOpenSet} (h : V ≤ U) (sec : SheafSection U) : SheafSection V :=
  { val := { map := restrictMap h sec.val.map
             morph_type := sec.val.morph_type
             current_spin := sec.val.current_spin
             is_valid := fun _ => IsHomeomorphism.id (TopCat.of V) }
    phase_shift := sec.phase_shift }

def AmalgamationReady {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V) : Prop :=
  sU.restrict (GeometricOpenSet.overlapLe_left U V) = sV.restrict (GeometricOpenSet.overlapLe_right U V) ∧
  sU.phase_shift * sU.val.current_spin.toSign = sV.phase_shift * sV.val.current_spin.toSign

def FamilyCompatible {ι : Type v} (U : ι → GeometricOpenSet) (s : ∀ i, SheafSection (U i)) : Prop :=
  ∀ i j, AmalgamationReady (s i) (s j)

noncomputable def constructIndexedGlobalSection {ι : Type v} [Nonempty ι] {U : GeometricOpenSet}
    (U_cover : ι → GeometricOpenSet) (h_cover : U = ⨆ i, U_cover i)
    (s : ∀ i, SheafSection (U_cover i)) (h_compat : FamilyCompatible U_cover s) : SheafSection U :=
  { val := { map := ContinuousMap.iSup_gluings (fun i => (s i).val.map) (by
              intro i j x hxi hxj
              have h_eq := (h_compat i j).1
              have h_eval := congr_arg (fun sec => sec.val.map ⟨x, ⟨hxi, hxj⟩⟩) h_eq
              dsimp [restrict, restrictMap] at h_eval
              exact Subtype.ext_iff.mp h_eval) h_cover
             morph_type := (s (Classical.arbitrary ι)).val.morph_type
             current_spin := (s (Classical.arbitrary ι)).val.current_spin
             is_valid := fun _ => IsHomeomorphism.id _ }
    phase_shift := (s (Classical.arbitrary ι)).phase_shift }

end SheafSection

/-! ## SECTION 4: GROTHENDIECK TOPOS & ANOMALY ABSORPTION -/
def TwistedPresheaf : (GeometricOpenSetᵒᵖ) ⥤ Type u where
  obj U := SheafSection (Opposite.unop U)
  map f sec := SheafSection.restrict f.unop sec

theorem twistedPresheaf_is_sheaf : Presheaf.IsSheaf TwistedPresheaf := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGlue]
  intro U ι U_cover h_cover s h_compat
  have h_cover_eq : Opposite.unop U = ⨆ i, U_cover i := by simpa using h_cover
  haveI : Nonempty ι := ⟨Classical.arbitrary ι⟩
  let sGlobal : TwistedPresheaf.obj U := SheafSection.constructIndexedGlobalSection U_cover h_cover_eq s h_compat
  refine ⟨sGlobal, ?, ?⟩
  · intro i
    ext
    · ext x; dsimp [TwistedPresheaf, SheafSection.constructIndexedGlobalSection, SheafSection.restrict, SheafSection.restrictMap]
      rfl
    · rfl
    · rfl
    · have h_c := (h_compat i (Classical.arbitrary ι)).2
      dsimp [TwistedPresheaf, SheafSection.constructIndexedGlobalSection]
      have h_spin : (s i).val.current_spin = (s (Classical.arbitrary ι)).val.current_spin := by
        have h1 := congr_arg (fun sec => sec.val.current_spin) (h_compat i (Classical.arbitrary ι)).1
        exact h1
      rw [h_spin] at h_c
      nlinarith [SpinDirection.toSign ((s (Classical.arbitrary ι)).val.current_spin)]
  · intro s' h_match
    ext
    · apply ContinuousMap.ext
      intro x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      rcases TopologicalSpace.Opens.mem_iSup.mp hx_cover with ⟨i, hi⟩
      have h_eval := congr_arg (fun sec => sec.val.map ⟨x.1, hi⟩) (h_match i)
      dsimp [TwistedPresheaf, SheafSection.restrict, SheafSection.restrictMap] at h_eval
      exact h_eval
    · obtain ⟨i₀⟩ := inferInstanceAs (Nonempty ι)
      exact congr_arg (fun sec => sec.val.morph_type) (h_match i₀)
    · obtain ⟨i₀⟩ := inferInstanceAs (Nonempty ι)
      exact congr_arg (fun sec => sec.val.current_spin) (h_match i₀)
    · obtain ⟨i₀⟩ := inferInstanceAs (Nonempty ι)
      exact congr_arg (fun sec => sec.phase_shift) (h_match i₀)

noncomputable def TwistedSheaf : Sheaf (Opens.grothendieckTopology AmbientSpace) (Type u) :=
  ⟨TwistedPresheaf, by simpa [Presheaf.IsSheaf, Opens.grothendieckTopology] using twistedPresheaf_is_sheaf⟩

structure LocalAnomaly (U : GeometricOpenSet) where
  cocycle_degree : Int
  is_active      : Bool

def resolveAnomalyWithJoker {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) : SheafSection U :=
  if anomaly.is_active ∧ anomaly.cocycle_degree ≠ 0 then
    { val := { sec.val with morph_type := MorphismType.joker }, phase_shift := 0 }
  else
    sec

theorem joker_absorbs_topological_anomaly {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U)
    (h_active : anomaly.is_active = true) (h_non_zero : anomaly.cocycle_degree ≠ 0) :
    (resolveAnomalyWithJoker sec anomaly).val.morph_type = MorphismType.joker := by
  unfold resolveAnomalyWithJoker
  simp [h_active, h_non_zero]
 
