# ToposCheck-ToposCheck.lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Nlinarith

set_option autoImplicit false
open CategoryTheory Opposite

universe u v

/-! ## SECTION 0: AMBIENT SPACE & TARGET SPACE -/

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

end GeometricOpenSet

variable (Y : Type u) [TopologicalSpace Y]

/-! ## SECTION 1: MORPHISM ALGEBRA & SPIN -/

inductive MorphismType where
  | standard : MorphismType
  | infinitesimal : MorphismType
  | joker : MorphismType
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
  mul_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

@[simp] lemma joker_absorbs (a : MorphismType) : joker * a = joker := rfl

end MorphismType

inductive SpinDirection where
  | left : SpinDirection
  | right : SpinDirection
  deriving DecidableEq, Repr

namespace SpinDirection

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
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  inv_mul_cancel a := by cases a <;> rfl

@[simp] lemma toSign_nonzero (s : SpinDirection) : s.toSign ≠ 0 := by
  cases s <;> decide

end SpinDirection

/-! ## SECTION 2: TERAMORPHISM ENGINE -/

@[ext]
structure Teramorphism (U : GeometricOpenSet) where
  map : C(U, Y)
  morph_type : MorphismType
  current_spin : SpinDirection

/-! ## SECTION 3: SOUND SHEAF SECTIONS & RESTRICTION -/

@[ext]
structure SheafSection (U : GeometricOpenSet) where
  val : Teramorphism Y U
  phase_shift : Int

namespace SheafSection

def restrict {U V : GeometricOpenSet} (h : V ≤ U) (sec : SheafSection Y U) : SheafSection Y V := {
  val := {
    map := sec.val.map.comp (ContinuousMap.inclusion h)
    morph_type := sec.val.morph_type
    current_spin := sec.val.current_spin
  }
  phase_shift := sec.phase_shift
}

@[simp]
lemma restrict_id {U : GeometricOpenSet} (sec : SheafSection Y U) :
    restrict Y (le_refl U) sec = sec := by
  ext <;> rfl

@[simp]
lemma restrict_comp {U V W : GeometricOpenSet} (h1 : V ≤ U) (h2 : W ≤ V) (sec : SheafSection Y U) :
    restrict Y h2 (restrict Y h1 sec) = restrict Y (le_trans h2 h1) sec := by
  ext <;> rfl

def AmalgamationReady {U V : GeometricOpenSet} (sU : SheafSection Y U) (sV : SheafSection Y V) : Prop :=
  sU.restrict Y (GeometricOpenSet.overlapLe_left U V) = sV.restrict Y (GeometricOpenSet.overlapLe_right U V) ∧
  sU.phase_shift * sU.val.current_spin.toSign = sV.phase_shift * sV.val.current_spin.toSign

def FamilyCompatible {ι : Type v} (U : ι → GeometricOpenSet) (s : ∀ i, SheafSection Y (U i)) : Prop :=
  ∀ i j, AmalgamationReady Y (s i) (s j)

-- Constructive global section handling empty and non-empty index types safely
noncomputable def constructIndexedGlobalSection {ι : Type v} {U : GeometricOpenSet}
    (U_cover : ι → GeometricOpenSet) (h_cover : U = ⨆ i, U_cover i)
    (s : ∀ i, SheafSection Y (U_cover i)) (h_compat : FamilyCompatible Y U_cover s) : SheafSection Y U :=
  if h_nonempty : Nonempty ι then
    let i₀ := Classical.choice h_nonempty
    { val := {
        map := ContinuousMap.iSup_gluings (fun i => (s i).val.map) (by
          intro i j x hxi hxj
          have h_eq := (h_compat i j).1
          have h_eval := congr_arg (fun sec => sec.val.map ⟨x, ⟨hxi, hxj⟩⟩) h_eq
          exact h_eval
        ) h_cover
        morph_type := (s i₀).val.morph_type
        current_spin := (s i₀).val.current_spin
      }
      phase_shift := (s i₀).phase_shift }
  else
    { val := {
        map := ContinuousMap.iSup_gluings (fun i => (s i).val.map) (by
          intro i j
          exfalso
          exact h_nonempty ⟨i⟩
        ) h_cover
        morph_type := MorphismType.standard
        current_spin := SpinDirection.left
      }
      phase_shift := 0 }

end SheafSection

/-! ## SECTION 4: LAWFUL PRESHEAF & SHEAF CONDITION -/

def TwistedPresheaf : (GeometricOpenSetᵒᵖ) ⥤ Type u where
  obj U := SheafSection Y (Opposite.unop U)
  map f sec := SheafSection.restrict Y (Quiver.Hom.unop f).le sec
  map_id X := by
    funext sec
    exact SheafSection.restrict_id Y sec
  map_comp f g := by
    funext sec
    exact SheafSection.restrict_comp Y (Quiver.Hom.unop f).le (Quiver.Hom.unop g).le sec

theorem twistedPresheaf_is_sheaf : Presheaf.IsSheaf (TwistedPresheaf Y) := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGlue]
  intro U ι U_cover h_cover s h_compat
  have h_cover_eq : Opposite.unop U = ⨆ i, U_cover i := by simpa using h_cover
  let sGlobal : (TwistedPresheaf Y).obj U := SheafSection.constructIndexedGlobalSection Y U_cover h_cover_eq s h_compat
  refine ⟨sGlobal, ?, ?⟩
  · intro i
    have h_ne : Nonempty ι := ⟨i⟩
    let i₀ := Classical.choice h_ne
    ext
    · ext x; rfl
    · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [dif_pos h_ne]
      have h_eq := (h_compat i i₀).1
      exact congr_arg (fun sec => sec.val.morph_type) h_eq
    · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [dif_pos h_ne]
      have h_eq := (h_compat i i₀).1
      exact congr_arg (fun sec => sec.val.current_spin) h_eq
    · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [dif_pos h_ne]
      have h_c := (h_compat i i₀).2
      have h_spin : (s i).val.current_spin = (s i₀).val.current_spin := by
        have h1 := (h_compat i i₀).1
        exact congr_arg (fun sec => sec.val.current_spin) h1
      rw [h_spin] at h_c
      cases (s i₀).val.current_spin <;>
      dsimp [SpinDirection.toSign] at h_c ⊢ <;> linarith
  · intro s' h_match
    by_cases h_ne : Nonempty ι
    · let i₀ := Classical.choice h_ne
      ext
      · apply ContinuousMap.ext
        intro x
        have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
        rcases TopologicalSpace.Opens.mem_iSup.mp hx_cover with ⟨i, hi⟩
        have h_eval := congr_arg (fun sec => sec.val.map ⟨x.1, hi⟩) (h_match i)
        exact h_eval
      · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
        rw [dif_pos h_ne]
        exact congr_arg (fun sec => sec.val.morph_type) (h_match i₀)
      · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
        rw [dif_pos h_ne]
        exact congr_arg (fun sec => sec.val.current_spin) (h_match i₀)
      · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
        rw [dif_pos h_ne]
        exact congr_arg (fun sec => sec.phase_shift) (h_match i₀)
    · ext
      · apply ContinuousMap.ext
        intro x
        exfalso
        have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
        rcases TopologicalSpace.Opens.mem_iSup.mp hx_cover with ⟨i, _⟩
        exact h_ne ⟨i⟩
      · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
        rw [dif_neg h_ne]
      · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
        rw [dif_neg h_ne]
      · dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
        rw [dif_neg h_ne]

noncomputable def TwistedSheaf : Sheaf (Opens.grothendieckTopology AmbientSpace) (Type u) :=
  ⟨TwistedPresheaf Y, by simpa [Presheaf.IsSheaf, Opens.grothendieckTopology] using twistedPresheaf_is_sheaf Y⟩

structure LocalAnomaly (U : GeometricOpenSet) where
  cocycle_degree : Int
  is_active : Bool

def anomalyToMorphismType (anomaly : LocalAnomaly U) : MorphismType :=
  if anomaly.is_active ∧ anomaly.cocycle_degree ≠ 0 then MorphismType.joker else MorphismType.standard

def resolveAnomalyWithJoker {U : GeometricOpenSet} (sec : SheafSection Y U) (anomaly : LocalAnomaly U) : SheafSection Y U :=
  { val := { sec.val with morph_type := sec.val.morph_type * anomalyToMorphismType anomaly },
    phase_shift := if anomaly.is_active then 0 else sec.phase_shift }

theorem joker_absorbs_topological_anomaly {U : GeometricOpenSet} (sec : SheafSection Y U) (anomaly : LocalAnomaly U)
    (h_active : anomaly.is_active = true) (h_non_zero : anomaly.cocycle_degree ≠ 0) :
    (resolveAnomalyWithJoker Y sec anomaly).val.morph_type = MorphismType.joker := by
  unfold resolveAnomalyWithJoker anomalyToMorphismType
  simp [h_active, h_non_zero, MorphismType.joker_absorbs]
