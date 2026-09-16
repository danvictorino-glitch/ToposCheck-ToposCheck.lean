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

set_option autoImplicit false
open CategoryTheory Opposite

universe u

variable (X : Type u) [TopologicalSpace X]
variable (Y : Type u) [TopologicalSpace Y]

abbrev GeometricOpenSet := TopologicalSpace.Opens X

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

end MorphismType

inductive SpinDirection where
  | left : SpinDirection
  | right : SpinDirection
  deriving DecidableEq, Repr

namespace SpinDirection

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

end SpinDirection

/-! ## SECTION 2: LOCALLY CONSTANT METADATA -/

structure LocalMetadata (U : GeometricOpenSet X) where
  morph_type : U → MorphismType
  current_spin : U → SpinDirection
  phase_shift : U → Int
  is_loc_const_morph : ∀ x : U, ∃ V : GeometricOpenSet X, x.1 ∈ V ∧ V ≤ U ∧ ∀ y : V, morph_type ⟨y.1, V.2 y.2⟩ = morph_type x
  is_loc_const_spin : ∀ x : U, ∃ V : GeometricOpenSet X, x.1 ∈ V ∧ V ≤ U ∧ ∀ y : V, current_spin ⟨y.1, V.2 y.2⟩ = current_spin x
  is_loc_const_phase : ∀ x : U, ∃ V : GeometricOpenSet X, x.1 ∈ V ∧ V ≤ U ∧ ∀ y : V, phase_shift ⟨y.1, V.2 y.2⟩ = phase_shift x

namespace LocalMetadata

def mul {U : GeometricOpenSet X} (m1 m2 : LocalMetadata X U) : LocalMetadata X U where
  morph_type := fun x => m1.morph_type x * m2.morph_type x
  current_spin := fun x => m1.current_spin x * m2.current_spin x
  phase_shift := fun x => m1.phase_shift x + m2.phase_shift x
  is_loc_const_morph := fun x => by
    rcases m1.is_loc_const_morph x with ⟨V1, hx1, hV1U, hV1_eq⟩
    rcases m2.is_loc_const_morph x with ⟨V2, hx2, hV2U, hV2_eq⟩
    refine ⟨V1 ⊓ V2, ⟨hx1, hx2⟩, inf_le_left.trans hV1U, ?_⟩
    intro y
    dsimp
    have hy1 : m1.morph_type ⟨y.1, hV1U (inf_le_left y.2)⟩ = m1.morph_type x := hV1_eq ⟨y.1, y.2.1⟩
    have hy2 : m2.morph_type ⟨y.1, hV2U (inf_le_right y.2)⟩ = m2.morph_type x := hV2_eq ⟨y.1, y.2.2⟩
    rw [hy1, hy2]
  is_loc_const_spin := fun x => by
    rcases m1.is_loc_const_spin x with ⟨V1, hx1, hV1U, hV1_eq⟩
    rcases m2.is_loc_const_spin x with ⟨V2, hx2, hV2U, hV2_eq⟩
    refine ⟨V1 ⊓ V2, ⟨hx1, hx2⟩, inf_le_left.trans hV1U, ?_⟩
    intro y
    dsimp
    have hy1 : m1.current_spin ⟨y.1, hV1U (inf_le_left y.2)⟩ = m1.current_spin x := hV1_eq ⟨y.1, y.2.1⟩
    have hy2 : m2.current_spin ⟨y.1, hV2U (inf_le_right y.2)⟩ = m2.current_spin x := hV2_eq ⟨y.1, y.2.2⟩
    rw [hy1, hy2]
  is_loc_const_phase := fun x => by
    rcases m1.is_loc_const_phase x with ⟨V1, hx1, hV1U, hV1_eq⟩
    rcases m2.is_loc_const_phase x with ⟨V2, hx2, hV2U, hV2_eq⟩
    refine ⟨V1 ⊓ V2, ⟨hx1, hx2⟩, inf_le_left.trans hV1U, ?_⟩
    intro y
    dsimp
    have hy1 : m1.phase_shift ⟨y.1, hV1U (inf_le_left y.2)⟩ = m1.phase_shift x := hV1_eq ⟨y.1, y.2.1⟩
    have hy2 : m2.phase_shift ⟨y.1, hV2U (inf_le_right y.2)⟩ = m2.phase_shift x := hV2_eq ⟨y.1, y.2.2⟩
    rw [hy1, hy2]

instance {U : GeometricOpenSet X} : Mul (LocalMetadata X U) := ⟨mul X⟩

end LocalMetadata

@[ext] structure Teramorphism (U : GeometricOpenSet X) where
  map : C(U, Y)
  meta : LocalMetadata X U

@[ext] structure SheafSection (U : GeometricOpenSet X) where
  val : Teramorphism X Y U

namespace SheafSection

def restrict {U V : GeometricOpenSet X} (h : V ≤ U) (sec : SheafSection X Y U) : SheafSection X Y V := {
  val := {
    map := sec.val.map.comp (ContinuousMap.inclusion h)
    meta := {
      morph_type := fun x => sec.val.meta.morph_type ⟨x.1, h x.2⟩
      current_spin := fun x => sec.val.meta.current_spin ⟨x.1, h x.2⟩
      phase_shift := fun x => sec.val.meta.phase_shift ⟨x.1, h x.2⟩
      is_loc_const_morph := fun x => by
        rcases sec.val.meta.is_loc_const_morph ⟨x.1, h x.2⟩ with ⟨W, hxW, hWU, hW_eq⟩
        refine ⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, ?_⟩
        intro y; exact hW_eq ⟨y.1, y.2.1⟩
      is_loc_const_spin := fun x => by
        rcases sec.val.meta.is_loc_const_spin ⟨x.1, h x.2⟩ with ⟨W, hxW, hWU, hW_eq⟩
        refine ⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, ?_⟩
        intro y; exact hW_eq ⟨y.1, y.2.1⟩
      is_loc_const_phase := fun x => by
        rcases sec.val.meta.is_loc_const_phase ⟨x.1, h x.2⟩ with ⟨W, hxW, hWU, hW_eq⟩
        refine ⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, ?_⟩
        intro y; exact hW_eq ⟨y.1, y.2.1⟩
    }
  }
}

@[simp] lemma restrict_id {U : GeometricOpenSet X} (sec : SheafSection X Y U) : restrict X Y (le_refl U) sec = sec := by
  ext <;> rfl

@[simp] lemma restrict_comp {U V W : GeometricOpenSet X} (h1 : V ≤ U) (h2 : W ≤ V) (sec : SheafSection X Y U) :
    restrict X Y h2 (restrict X Y h1 sec) = restrict X Y (le_trans h2 h1) sec := by
  ext <;> rfl

def AmalgamationReady {U V : GeometricOpenSet X} (sU : SheafSection X Y U) (sV : SheafSection X Y V) : Prop :=
  sU.restrict X Y inf_le_left = sV.restrict X Y inf_le_right

def FamilyCompatible {ι : Type u} (U : ι → GeometricOpenSet X) (s : ∀ i, SheafSection X Y (U i)) : Prop :=
  ∀ i j, AmalgamationReady X Y (s i) (s j)

noncomputable def glueContinuousMap {ι : Type u} {U : GeometricOpenSet X} (U_cover : ι → GeometricOpenSet X)
    (h_cover : U = ⨆ i, U_cover i) (maps : ∀ i, C(U_cover i, Y))
    (h_compat : ∀ i j (x : X) (hi : x ∈ U_cover i) (hj : x ∈ U_cover j), maps i ⟨x, hi⟩ = maps j ⟨x, hj⟩) : C(U, Y) :=
  ContinuousMap.mk (fun x =>
    have hx : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
    let i := (TopologicalSpace.Opens.mem_iSup.mp hx).choose
    let hi := (TopologicalSpace.Opens.mem_iSup.mp hx).choose_spec
    maps i ⟨x.1, hi⟩)
    (by
      rw [continuous_iff_continuousAt]
      intro x
      have hx : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx).choose_spec
      have h_cont := (maps i).continuous
      rw [continuous_iff_continuousAt] at h_cont
      have h_incl : ContinuousAt (ContinuousMap.inclusion (le_iSup U_cover i)) ⟨x.1, hi⟩ :=
        (ContinuousMap.inclusion _).continuous.continuousAt
      exact ContinuousAt.comp (h_cont ⟨x.1, hi⟩) h_incl)

noncomputable def constructIndexedGlobalSection {ι : Type u} {U : GeometricOpenSet X} (U_cover : ι → GeometricOpenSet X)
    (h_cover : U = ⨆ i, U_cover i) (s : ∀ i, SheafSection X Y (U_cover i)) (h_compat : FamilyCompatible X Y U_cover s) :
    SheafSection X Y U := {
  val := {
    map := glueContinuousMap X Y U_cover h_cover (fun i => (s i).val.map) (by
      intro i j x hi hj
      have h_eq := h_compat i j
      exact congr_arg (fun sec => sec.val.map ⟨x, ⟨hi, hj⟩⟩) h_eq)
    meta := {
      morph_type := fun x =>
        have hx : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
        let i := (TopologicalSpace.Opens.mem_iSup.mp hx).choose
        let hi := (TopologicalSpace.Opens.mem_iSup.mp hx).choose_spec
        (s i).val.meta.morph_type ⟨x.1, hi⟩
      current_spin := fun x =>
        have hx : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
        let i := (TopologicalSpace.Opens.mem_iSup.mp hx).choose
        let hi := (TopologicalSpace.Opens.mem_iSup.mp hx).choose_spec
        (s i).val.meta.current_spin ⟨x.1, hi⟩
      phase_shift := fun x =>
        have hx : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
        let i := (TopologicalSpace.Opens.mem_iSup.mp hx).choose
        let hi := (TopologicalSpace.Opens.mem_iSup.mp hx).choose_spec
        (s i).val.meta.phase_shift ⟨x.1, hi⟩
      is_loc_const_morph := fun x => by
        have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
        let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
        let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
        rcases (s i).val.meta.is_loc_const_morph ⟨x.1, hi⟩ with ⟨W, hxW, hWU, hW_eq⟩
        refine ⟨W, hxW, hWU.trans (by rw [h_cover]; exact le_iSup U_cover i), ?_⟩
        intro y
        dsimp
        have h_eq := h_compat i ((TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover])).choose)
        have h_eval := congr_arg (fun sec => sec.val.meta.morph_type ⟨y.1, ⟨hWU y.2, (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover])).choose_spec⟩⟩) h_eq
        rw [← h_eval]
        exact hW_eq ⟨y.1, hWU y.2⟩
      is_loc_const_spin := fun x => by
        have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
        let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
        let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
        rcases (s i).val.meta.is_loc_const_spin ⟨x.1, hi⟩ with ⟨W, hxW, hWU, hW_eq⟩
        refine ⟨W, hxW, hWU.trans (by rw [h_cover]; exact le_iSup U_cover i), ?_⟩
        intro y
        dsimp
        have h_eq := h_compat i ((TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover])).choose)
        have h_eval := congr_arg (fun sec => sec.val.meta.current_spin ⟨y.1, ⟨hWU y.2, (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover])).choose_spec⟩⟩) h_eq
        rw [← h_eval]
        exact hW_eq ⟨y.1, hWU y.2⟩
      is_loc_const_phase := fun x => by
        have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
        let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
        let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
        rcases (s i).val.meta.is_loc_const_phase ⟨x.1, hi⟩ with ⟨W, hxW, hWU, hW_eq⟩
        refine ⟨W, hxW, hWU.trans (by rw [h_cover]; exact le_iSup U_cover i), ?_⟩
        intro y
        dsimp
        have h_eq := h_compat i ((TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover])).choose)
        have h_eval := congr_arg (fun sec => sec.val.meta.phase_shift ⟨y.1, ⟨hWU y.2, (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover])).choose_spec⟩⟩) h_eq
        rw [← h_eval]
        exact hW_eq ⟨y.1, hWU y.2⟩
    }
  }
}

end SheafSection

/-! ## SECTION 3: PRESHEAF & SHEAF CONDITION -/

def TwistedPresheaf : (GeometricOpenSet X)ᵒᵖ ⥤ Type u where
  obj U := SheafSection X Y (Opposite.unop U)
  map f sec := SheafSection.restrict X Y (Quiver.Hom.unop f).le sec
  map_id X := by funext sec; exact SheafSection.restrict_id X Y sec
  map_comp f g := by funext sec; exact SheafSection.restrict_comp X Y (Quiver.Hom.unop f).le (Quiver.Hom.unop g).le sec

theorem twistedPresheaf_is_sheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X) (TwistedPresheaf X Y) := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGlue]
  intro U ι U_cover h_cover s h_compat
  have h_cover_eq : Opposite.unop U = ⨆ i, U_cover i := by simpa using h_cover
  let sGlobal : (TwistedPresheaf X Y).obj U := SheafSection.constructIndexedGlobalSection X Y U_cover h_cover_eq s h_compat
  refine ⟨sGlobal, ?, ?⟩
  · intro i
    ext
    · apply ContinuousMap.ext; intro x
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection, SheafSection.glueContinuousMap]
      have h_eq := h_compat i ((TopologicalSpace.Opens.mem_iSup.mp (by rw [← h_cover_eq]; exact (le_iSup U_cover i) x.2)).choose)
      exact congr_arg (fun sec => sec.val.map ⟨x.1, ⟨x.2, (TopologicalSpace.Opens.mem_iSup.mp (by rw [← h_cover_eq]; exact (le_iSup U_cover i) x.2)).choose_spec⟩⟩) h_eq
    · ext x
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      have h_eq := h_compat i ((TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose)
      exact congr_arg (fun sec => sec.val.meta.morph_type ⟨x.1, ⟨x.2, (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose_spec⟩⟩) h_eq
    · ext x
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      have h_eq := h_compat i ((TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose)
      exact congr_arg (fun sec => sec.val.meta.current_spin ⟨x.1, ⟨x.2, (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose_spec⟩⟩) h_eq
    · ext x
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      have h_eq := h_compat i ((TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose)
      exact congr_arg (fun sec => sec.val.meta.phase_shift ⟨x.1, ⟨x.2, (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose_spec⟩⟩) h_eq
  · intro s' h_match
    ext
    · apply ContinuousMap.ext; intro x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
      have h_eval := congr_arg (fun (sec : SheafSection X Y (U_cover i)) => sec.val.map ⟨x.1, hi⟩) (h_match i)
      exact h_eval
    · ext x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
      have h_eval := congr_arg (fun (sec : SheafSection X Y (U_cover i)) => sec.val.meta.morph_type ⟨x.1, hi⟩) (h_match i)
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [← h_eval]
    · ext x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
      have h_eval := congr_arg (fun (sec : SheafSection X Y (U_cover i)) => sec.val.meta.current_spin ⟨x.1, hi⟩) (h_match i)
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [← h_eval]
    · ext x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
      have h_eval := congr_arg (fun (sec : SheafSection X Y (U_cover i)) => sec.val.meta.phase_shift ⟨x.1, hi⟩) (h_match i)
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [← h_eval]

noncomputable def TwistedSheaf : Sheaf (Opens.grothendieckTopology X) (Type u) :=
  ⟨TwistedPresheaf X Y, twistedPresheaf_is_sheaf X Y⟩
