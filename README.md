# ToposCheck-ToposCheck.lean
/-! # Fully Refined ToposCheck.lean -/

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
import Mathlib.Topology.ContinuousFunction.Board

set_option autoImplicit false

open CategoryTheory Opposite

universe u v

/-! ## SECTION 0: AMBIENT SPACE -/

axiom AmbientSpace : Type u
axiom ambientTopology : TopologicalSpace AmbientSpace
noncomputable instance : TopologicalSpace AmbientSpace := ambientTopology

/-! ## SECTION 1: GEOMETRIC OPEN SETS AS A GENUINE LATTICE -/

abbrev GeometricOpenSet := TopologicalSpace.Opens AmbientSpace

namespace GeometricOpenSet

def union (U V : GeometricOpenSet) : GeometricOpenSet := U ⊔ V
def overlap (U V : GeometricOpenSet) : GeometricOpenSet := U ⊓ V

@[simp] lemma union_comm (U V : GeometricOpenSet) : union U V = union V U := sup_comm U V
@[simp] lemma overlap_comm (U V : GeometricOpenSet) : overlap U V = overlap V U := inf_comm U V

lemma union_assoc (U V W : GeometricOpenSet) : union (union U V) W = union U (union V W) := sup_assoc U V W
lemma overlap_assoc (U V W : GeometricOpenSet) : overlap (overlap U V) W = overlap U (overlap V W) := inf_assoc U V W

@[simp] lemma union_idem (U : GeometricOpenSet) : union U U = U := sup_idem U
@[simp] lemma overlap_idem (U : GeometricOpenSet) : overlap U U = U := inf_idem U

@[simp] lemma absorption_union_overlap (U V : GeometricOpenSet) : union (overlap U V) U = U := sup_inf_self U V
@[simp] lemma absorption_overlap_union (U V : GeometricOpenSet) : overlap (union U V) U = U := inf_sup_self U V

lemma overlap_union_distrib (U V W : GeometricOpenSet) :
    overlap U (union V W) = union (overlap U V) (overlap U W) := inf_sup_left U V W

lemma overlapLe_left (U V : GeometricOpenSet) : overlap U V ≤ U := inf_le_left
lemma overlapLe_right (U V : GeometricOpenSet) : overlap U V ≤ V := inf_le_right
lemma unionLe_left (U V : GeometricOpenSet) : U ≤ union U V := le_sup_left
lemma unionLe_right (U V : GeometricOpenSet) : V ≤ union U V := le_sup_right

lemma overlap_mono {U U' V V' : GeometricOpenSet} (hU : U ≤ U') (hV : V ≤ V') :
    overlap U V ≤ overlap U' V' := inf_le_inf hU hV

end GeometricOpenSet

/-! ## SECTION 2: MORPHISM TYPES AND SPIN -/

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
  mul_comm a b := by decide
  mul_assoc a b c := by decide
  one_mul a := by decide
  mul_one a := by decide

@[simp] lemma joker_mul_absorbs (a : MorphismType) : joker * a = joker := rfl
@[simp] lemma mul_joker_absorbs (a : MorphismType) : a * joker = joker := by decide

lemma eq_standard_of_idem_of_ne_joker {a : MorphismType} (h : a * a = a) (hj : a ≠ joker) :
    a = standard := by
  cases a with
  | standard => rfl
  | infinitesimal => simp [comp] at h
  | joker => exact absurd rfl hj

end MorphismType

inductive SpinDirection where
  | left : SpinDirection
  | right : SpinDirection
  deriving DecidableEq, Repr

namespace SpinDirection

def toggle : SpinDirection → SpinDirection
  | left => right
  | right => left

def invert : SpinDirection → SpinDirection := toggle

lemma toggle_involution (s : SpinDirection) : toggle (toggle s) = s := by cases s <;> rfl

@[simp] lemma invert_involution (s : SpinDirection) : invert (invert s) = s :=
  toggle_involution s

def isEquivalence (s1 s2 : SpinDirection) : Bool := s1 == s2

lemma toggle_bijective : Function.Bijective toggle := by
  constructor
  · intro s t h; cases s <;> cases t <;> first | rfl | exact absurd h (by decide)
  · intro s; exact ⟨toggle s, toggle_involution s⟩

end SpinDirection

instance : CommGroup SpinDirection where
  mul a b := match a, b with
    | SpinDirection.left, SpinDirection.left => SpinDirection.left
    | SpinDirection.left, SpinDirection.right => SpinDirection.right
    | SpinDirection.right, SpinDirection.left => SpinDirection.right
    | SpinDirection.right, SpinDirection.right => SpinDirection.left
  one := SpinDirection.left
  inv a := a
  mul_assoc a b c := by decide
  mul_comm a b := by decide
  one_mul a := by decide
  mul_one a := by decide
  inv_mul_cancel a := by decide

/-! ## SECTION 3: TERAMORPHISM CORE ENGINE -/

structure Teramorphism (U V : GeometricOpenSet) where
  map : C(U, V)
  morph_type : MorphismType
  current_spin : SpinDirection
  is_valid : morph_type = MorphismType.standard → IsHomeomorphism map

namespace Teramorphism

@[simp] def spinLeftToRight {U V : GeometricOpenSet} (t : Teramorphism U V) : Teramorphism U V :=
  match t.current_spin with
  | SpinDirection.left => { t with current_spin := SpinDirection.right }
  | SpinDirection.right => t

@[simp] def toggleSpin {U V : GeometricOpenSet} (t : Teramorphism U V) : Teramorphism U V :=
  { t with current_spin := t.current_spin.toggle }

@[simp] def identity (U : GeometricOpenSet) : Teramorphism U U :=
  { map := ContinuousMap.id U
    morph_type := MorphismType.standard
    current_spin := SpinDirection.right
    is_valid := fun _ => Homeomorph.isHomeomorphism (Homeomorph.refl U) }

def compose {U V W : GeometricOpenSet} (t1 : Teramorphism U V) (t2 : Teramorphism V W) :
    Teramorphism U W :=
  { map := t2.map.comp t1.map
    morph_type := t1.morph_type * t2.morph_type
    current_spin := if t1.current_spin = t2.current_spin then t1.current_spin else SpinDirection.right
    is_valid := by
      intro h
      have h1 : t1.morph_type = MorphismType.standard ∧ t2.morph_type = MorphismType.standard := by
        rcases t1.morph_type with _ | _ | _ <;> rcases t2.morph_type with _ | _ | _ <;>
          simp_all [MorphismType.comp, HMul.hMul, Mul.mul]
      exact IsHomeomorphism.comp (t2.is_valid h1.2) (t1.is_valid h1.1) }

infixl:90 " ∘ᵗ " => compose

lemma compose_map_apply {U V W : GeometricOpenSet} (t1 : Teramorphism U V)
    (t2 : Teramorphism V W) (x : U) : (t1 ∘ᵗ t2).map x = t2.map (t1.map x) := rfl

lemma left_id {U V : GeometricOpenSet} (t : Teramorphism U V) : identity U ∘ᵗ t = t := by
  cases t; simp [compose, identity]

lemma right_id {U V : GeometricOpenSet} (t : Teramorphism U V) : t ∘ᵗ identity V = t := by
  cases t; simp [compose, identity]

lemma compose_assoc {U V W Y : GeometricOpenSet} (t1 : Teramorphism U V)
    (t2 : Teramorphism V W) (t3 : Teramorphism W Y) :
    (t1 ∘ᵗ t2) ∘ᵗ t3 = t1 ∘ᵗ (t2 ∘ᵗ t3) := by
  cases t1; cases t2; cases t3
  simp [compose, mul_assoc]

def isInvertible {U V : GeometricOpenSet} (t : Teramorphism U V) : Prop :=
  t.morph_type = MorphismType.standard

def isJoker {U V : GeometricOpenSet} (t : Teramorphism U V) : Prop :=
  t.morph_type = MorphismType.joker

lemma joker_composition_left {U V W : GeometricOpenSet} (t1 : Teramorphism U V)
    (t2 : Teramorphism V W) (h : t1.isJoker) : (t1 ∘ᵗ t2).isJoker := by
  simp [compose, isJoker] at h ⊢; simp [h]

lemma joker_composition_right {U V W : GeometricOpenSet} (t1 : Teramorphism U V)
    (t2 : Teramorphism V W) (h : t2.isJoker) : (t1 ∘ᵗ t2).isJoker := by
  simp [compose, isJoker] at h ⊢; simp [h]

noncomputable def toHomeomorph {U V : GeometricOpenSet} (t : Teramorphism U V)
    (h : t.isInvertible) : U ≃ₜ V :=
  (t.is_valid h).homeomorph

noncomputable def inverse {U V : GeometricOpenSet} (t : Teramorphism U V)
    (h : t.isInvertible) : Teramorphism V U :=
  { map := (t.toHomeomorph h).symm.toContinuousMap
    morph_type := MorphismType.standard
    current_spin := t.current_spin
    is_valid := fun _ => Homeomorph.isHomeomorphism (t.toHomeomorph h).symm }

lemma compose_inverse_left {U V : GeometricOpenSet} (t : Teramorphism U V)
    (h : t.isInvertible) :
    (t.inverse h).morph_type = MorphismType.standard ∧
      ∀ x : V, (t ∘ᵗ t.inverse h).map ((t.toHomeomorph h) ((t.toHomeomorph h).symm x)) =
        (t.toHomeomorph h) ((t.toHomeomorph h).symm x) := by
  refine ⟨rfl, ?_⟩
  intro x
  simp [compose_map_apply, inverse, Homeomorph.apply_symm_apply]

lemma inverse_right_cancel {U V : GeometricOpenSet} (t : Teramorphism U V)
    (h : t.isInvertible) (x : V) : t.map ((t.inverse h).map x) = x := by
  simp [inverse, toHomeomorph, IsHomeomorphism.homeomorph_apply, Homeomorph.apply_symm_apply]

lemma inverse_left_cancel {U V : GeometricOpenSet} (t : Teramorphism U V)
    (h : t.isInvertible) (x : U) : (t.inverse h).map (t.map x) = x := by
  simp [inverse, toHomeomorph, IsHomeomorphism.homeomorph_apply, Homeomorph.symm_apply_apply]

end Teramorphism

instance : Category GeometricOpenSet where
  Hom U V := Teramorphism U V
  id U := Teramorphism.identity U
  comp t1 t2 := t1 ∘ᵗ t2
  id_comp := Teramorphism.left_id
  comp_id := Teramorphism.right_id
  assoc := Teramorphism.compose_assoc

/-! ## SECTION 4: SHEAF SECTION STRUCTURE & ARBITRARY GLUING -/

structure SheafSection (U : GeometricOpenSet) where
  val : Teramorphism U U

namespace SheafSection

/-- Restricts a continuous map `f : U → U` to `V ⊆ U`. -/
noncomputable def restrictMap {U V : GeometricOpenSet} (h : V ≤ U) (f : C(U, U)) : C(V, V) where
  toFun x := ⟨(f ⟨x.1, h x.2⟩).1, (f ⟨x.1, h x.2⟩).2⟩
  continuous_toFun := by
    continuous_subtype_pullback

noncomputable def restrict {U V : GeometricOpenSet} (h : V ≤ U) (sec : SheafSection U) : SheafSection V :=
  { val :=
      { map := restrictMap h sec.val.map
        morph_type := sec.val.morph_type
        current_spin := sec.val.current_spin
        is_valid := fun _ => IsHomeomorphism.id (TopCat.of V) } }

lemma restrict_trans {U V W : GeometricOpenSet} (hVU : V ≤ U) (hWV : W ≤ V) (sec : SheafSection U) :
    (sec.restrict hVU).restrict hWV = sec.restrict (le_trans hWV hVU) := by
  ext
  · ext x; rfl
  · rfl
  · rfl

@[simp] lemma restrict_refl {U : GeometricOpenSet} (sec : SheafSection U) :
    sec.restrict (le_refl U) = sec := by
  cases sec
  ext
  · ext x; rfl
  · rfl
  · rfl

def AmalgamationReady {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V) : Prop :=
  sU.restrict (GeometricOpenSet.overlapLe_left U V) =
    sV.restrict (GeometricOpenSet.overlapLe_right U V)

lemma amalgamationReady_symm {U V : GeometricOpenSet} (sU : SheafSection U)
    (sV : SheafSection V) (h : AmalgamationReady sU sV) : AmalgamationReady sV sU := by
  simpa [AmalgamationReady, GeometricOpenSet.overlap_comm] using h.symm

def IsGluedSection {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V)
    (sGlobal : SheafSection (GeometricOpenSet.union U V)) : Prop :=
  sGlobal.restrict (GeometricOpenSet.unionLe_left U V) = sU ∧
    sGlobal.restrict (GeometricOpenSet.unionLe_right U V) = sV

noncomputable def constructGlobalSection {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) : SheafSection (GeometricOpenSet.union U V) :=
  { val :=
    { map := ContinuousMap.glue U V sU.val.map sV.val.map (by
        intro x hxU hxV
        have h_eq : (sU.restrict (GeometricOpenSet.overlapLe_left U V)).val.map ⟨x, ⟨hxU, hxV⟩⟩ =
                    (sV.restrict (GeometricOpenSet.overlapLe_right U V)).val.map ⟨x, ⟨hxU, hxV⟩⟩ := by
          rw [h_ready]
        exact Subtype.ext_iff.mp (congr_arg Subtype.val h_eq))
      morph_type := sU.val.morph_type * sV.val.morph_type
      current_spin := if sU.val.current_spin = sV.val.current_spin then sU.val.current_spin else SpinDirection.right
      is_valid := fun _ => IsHomeomorphism.id _ } }

theorem glue_synthesis_correct {U V : GeometricOpenSet} (sU : SheafSection U)
    (sV : SheafSection V) (h_ready : AmalgamationReady sU sV) :
    IsGluedSection sU sV (constructGlobalSection sU sV h_ready) := by
  constructor
  · ext
    · ext x; simp [constructGlobalSection, restrict, restrictMap, ContinuousMap.glue]
    · simp [constructGlobalSection, restrict]
    · simp [constructGlobalSection, restrict]
  · ext
    · ext x; simp [constructGlobalSection, restrict, restrictMap, ContinuousMap.glue]
    · simp [constructGlobalSection, restrict]
    · simp [constructGlobalSection, restrict]

theorem locality {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    sU.restrict (GeometricOpenSet.overlapLe_left U V) =
      sV.restrict (GeometricOpenSet.overlapLe_right U V) := h_ready

theorem gluing {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    ∃ sGlobal : SheafSection (GeometricOpenSet.union U V), IsGluedSection sU sV sGlobal :=
  ⟨constructGlobalSection sU sV h_ready, glue_synthesis_correct sU sV h_ready⟩

def FamilyCompatible {ι : Type v} (U : ι → GeometricOpenSet) (s : ∀ i, SheafSection (U i)) : Prop :=
  ∀ i j, (s i).restrict (GeometricOpenSet.overlapLe_left (U i) (U j)) =
    (s j).restrict (GeometricOpenSet.overlapLe_right (U i) (U j))

theorem section_uniqueness {U V : GeometricOpenSet}
    {s₁ s₂ : SheafSection (GeometricOpenSet.union U V)} (hMap : s₁.val.map = s₂.val.map)
    (hType : s₁.val.morph_type = s₂.val.morph_type)
    (hSpin : s₁.val.current_spin = s₂.val.current_spin) : s₁ = s₂ := by
  cases s₁ with | mk t₁ => cases s₂ with | mk t₂ => cases hMap; cases hType; cases hSpin; rfl

theorem indexed_locality {ι : Type v} [Nonempty ι] {U : GeometricOpenSet} {U_cover : ι → GeometricOpenSet}
    (h_cover : U = ⨆ i, U_cover i) (s₁ s₂ : SheafSection U)
    (h_eq : ∀ i, s₁.restrict (le_iSup U_cover i ⬝ (ge_of_eq h_cover)) =
      s₂.restrict (le_iSup U_cover i ⬝ (ge_of_eq h_cover))) : s₁ = s₂ := by
  cases s₁ with | mk t₁ => cases s₂ with | mk t₂ =>
    ext
    · apply ContinuousMap.ext
      intro x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover]
      rcases TopologicalSpace.Opens.mem_iSup.mp hx_cover with ⟨i, hi⟩
      let x_i : U_cover i := ⟨x.1, hi⟩
      have h_eval := congr_arg (fun sec => sec.val.map x_i) (h_eq i)
      dsimp [SheafSection.restrict] at h_eval
      exact h_eval
    · obtain ⟨i₀⟩ := inferInstanceAs (Nonempty ι)
      exact congr_arg (fun sec => sec.val.morph_type) (h_eq i₀)
    · obtain ⟨i₀⟩ := inferInstanceAs (Nonempty ι)
      exact congr_arg (fun sec => sec.val.current_spin) (h_eq i₀)

/-- Refinement 1: Upgraded arbitrary indexed continuous map gluing via `ContinuousMap.gluings`. -/
noncomputable def constructIndexedGlobalSection {ι : Type v} [Nonempty ι] {U : GeometricOpenSet}
    (U_cover : ι → GeometricOpenSet) (h_cover : U = ⨆ i, U_cover i)
    (s : ∀ i, SheafSection (U_cover i)) (h_compat : FamilyCompatible U_cover s) :
    SheafSection U :=
  { val :=
      { map := ContinuousMap.gluings (fun i => (s i).val.map) (by
          intro i j x hxi hxj
          have h_eq := congr_arg (fun sec => sec.val.map ⟨x, ⟨hxi, hxj⟩⟩) (h_compat i j)
          dsimp [SheafSection.restrict, restrictMap] at h_eq
          exact Subtype.ext_iff.mp (congr_arg Subtype.val h_eq)) h_cover
        morph_type := (s (Classical.arbitrary ι)).val.morph_type
        current_spin := (s (Classical.arbitrary ι)).val.current_spin
        is_valid := fun _ => IsHomeomorphism.id _ } }

noncomputable instance (U V : GeometricOpenSet) (sU : SheafSection U) (sV : SheafSection V) :
    Decidable (AmalgamationReady sU sV) := by classical; dsimp [AmalgamationReady]; infer_instance

noncomputable instance (U V : GeometricOpenSet) (sU : SheafSection U) (sV : SheafSection V)
    (sGlobal : SheafSection (GeometricOpenSet.union U V)) :
    Decidable (IsGluedSection sU sV sGlobal) := by classical; dsimp [IsGluedSection]; infer_instance

/-! ### Germs and Stalks -/

structure PointedSection (x : AmbientSpace) where
  U : GeometricOpenSet
  mem : x ∈ U
  sec : SheafSection U

def SameGerm {x : AmbientSpace} (p q : PointedSection x) : Prop :=
  ∃ (W : GeometricOpenSet) (hW : x ∈ W) (hWp : W ≤ p.U) (hWq : W ≤ q.U),
    p.sec.restrict hWp = q.sec.restrict hWq

lemma sameGerm_refl {x : AmbientSpace} (p : PointedSection x) : SameGerm p p :=
  ⟨p.U, p.mem, le_refl _, le_refl _, by simp⟩

lemma sameGerm_symm {x : AmbientSpace} {p q : PointedSection x} (h : SameGerm p q) : SameGerm q p := by
  obtain ⟨W, hW, hWp, hWq, heq⟩ := h
  exact ⟨W, hW, hWq, hWp, heq.symm⟩

lemma sameGerm_trans {x : AmbientSpace} {p q r : PointedSection x}
    (h1 : SameGerm p q) (h2 : SameGerm q r) : SameGerm p r := by
  obtain ⟨W1, hW1, hW1p, hW1q, heq1⟩ := h1
  obtain ⟨W2, hW2, hW2q, hW2r, heq2⟩ := h2
  refine ⟨GeometricOpenSet.overlap W1 W2, ⟨hW1, hW2⟩,
    le_trans (GeometricOpenSet.overlapLe_left W1 W2) hW1p,
    le_trans (GeometricOpenSet.overlapLe_right W1 W2) hW2r, ?_⟩
  have e1 := congr_arg (fun s => s.restrict (GeometricOpenSet.overlapLe_left W1 W2)) heq1
  have e2 := congr_arg (fun s => s.restrict (GeometricOpenSet.overlapLe_right W1 W2)) heq2
  simp only [SheafSection.restrict_trans] at e1 e2
  exact e1.trans e2

instance sameGermSetoid (x : AmbientSpace) : Setoid (PointedSection x) where
  r := SameGerm
  iseqv := ⟨sameGerm_refl, sameGerm_symm, sameGerm_trans⟩

def Stalk (x : AmbientSpace) := Quotient (sameGermSetoid x)

def germ {x : AmbientSpace} (U : GeometricOpenSet) (hx : x ∈ U) (sec : SheafSection U) : Stalk x :=
  Quotient.mk _ ⟨U, hx, sec⟩

lemma germ_restrict {x : AmbientSpace} {U V : GeometricOpenSet} (hVU : V ≤ U)
    (hx : x ∈ V) (sec : SheafSection U) :
    germ V hx (sec.restrict hVU) = germ U (hVU hx) sec := by
  apply Quotient.sound
  exact ⟨V, hx, le_refl V, hVU, by simp⟩

end SheafSection

/-! ## SECTION 5: PRESHEAF FUNCTOR AND GROTHENDIECK TOPOLOGY -/

def AlphaPresheaf : (GeometricOpenSetᵒᵖ) ⥤ Type u where
  obj U := SheafSection (Opposite.unop U)
  map f sec := SheafSection.restrict f.unop sec

open TopCat

theorem alphaPresheaf_is_sheaf : Presheaf.IsSheaf AlphaPresheaf := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGlue]
  intro U ι U_cover h_cover s h_compat
  have h_cover_eq : Opposite.unop U = ⨆ i, U_cover i := by simpa using h_cover
  haveI : Nonempty ι := ⟨Classical.arbitrary ι⟩
  let sGlobal : AlphaPresheaf.obj U := SheafSection.constructIndexedGlobalSection U_cover h_cover_eq s h_compat
  refine ⟨sGlobal, ?_, ?_⟩
  · intro i; dsimp [AlphaPresheaf, SheafSection.constructIndexedGlobalSection]; simp [sGlobal]
  · intro s' h_match
    apply SheafSection.indexed_locality h_cover_eq
    intro i
    rw [h_match i]
    simp [sGlobal]

theorem alphaPresheaf_isSheaf_opens :
    Presieve.IsSheaf (Opens.grothendieckTopology AmbientSpace) AlphaPresheaf := by
  simpa [Presheaf.IsSheaf, Opens.grothendieckTopology] using alphaPresheaf_is_sheaf

noncomputable def AlphaSheaf : Sheaf (Opens.grothendieckTopology AmbientSpace) (Type u) :=
  ⟨AlphaPresheaf, alphaPresheaf_isSheaf_opens⟩

def activateMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app _ sec := { val := Teramorphism.spinLeftToRight sec.val }

def toggleMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app _ sec := { val := Teramorphism.toggleSpin sec.val }

def spinAct (s : SpinDirection) {U : GeometricOpenSet} (sec : SheafSection U) : SheafSection U :=
  match s with
  | SpinDirection.left => sec
  | SpinDirection.right => { val := Teramorphism.toggleSpin sec.val }

instance (U : GeometricOpenSet) : MulAction SpinDirection (SheafSection U) where
  smul := spinAct
  one_smul sec := by simp [spinAct]
  mul_smul a b sec := by
    cases a <;> cases b <;> simp [spinAct, Teramorphism.toggleSpin, SpinDirection.toggle_involution]

theorem toggle_motive_twice_id : toggleMotiveSheaf ≫ toggleMotiveSheaf = 𝟙 AlphaPresheaf := by
  ext U sec; simp [toggleMotiveSheaf, Teramorphism.toggleSpin, SpinDirection.toggle_involution]

lemma nattrans_compose_app {F G H : (GeometricOpenSetᵒᵖ) ⥤ Type u} (α : F ⟹ G) (β : G ⟹ H)
    (U : GeometricOpenSetᵒᵖ) (x : F.obj U) : (α ≫ β).app U x = β.app U (α.app U x) := rfl

def activateMotiveSheafTwice : AlphaPresheaf ⟹ AlphaPresheaf :=
  activateMotiveSheaf ≫ activateMotiveSheaf

lemma activate_twice_left {U : GeometricOpenSet} (sec : SheafSection U)
    (h : sec.val.current_spin = SpinDirection.left) :
    (activateMotiveSheafTwice.app (Opposite.op U) sec).val.current_spin = SpinDirection.right := by
  simp [activateMotiveSheafTwice, activateMotiveSheaf, Teramorphism.spinLeftToRight, h]

theorem activate_motive_idempotent :
    activateMotiveSheaf ≫ activateMotiveSheaf = activateMotiveSheaf := by
  ext U sec
  cases h : sec.val.current_spin <;> simp [activateMotiveSheaf, Teramorphism.spinLeftToRight, h]

/-! ## SECTION 6: ANOMALY RESOLUTION FRAMEWORK -/

structure LocalAnomaly (U : GeometricOpenSet) where
  is_broken : Bool

def resolveWithJoker {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    SheafSection U :=
  if anomaly.is_broken then { val := { sec.val with morph_type := MorphismType.joker } } else sec

def resolveWithJokerExcept {U : GeometricOpenSet} (sec : SheafSection U)
    (anomaly : LocalAnomaly U) : Except String (SheafSection U) :=
  if anomaly.is_broken then Except.error "Local anomaly detected" else Except.ok sec

def resolveWithJokerExceptT {U : GeometricOpenSet} (sec : SheafSection U)
    (anomaly : LocalAnomaly U) : ExceptT String Id (SheafSection U) :=
  if anomaly.is_broken then throw "Local anomaly detected" else pure sec

def restrictAnomaly {U V : GeometricOpenSet} (_h : V ≤ U) (anomaly : LocalAnomaly U) : LocalAnomaly V :=
  { is_broken := anomaly.is_broken }

theorem resolveWithJoker_restrict_commutes {U V : GeometricOpenSet} (h : V ≤ U)
    (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    resolveWithJoker (sec.restrict h) (restrictAnomaly h anomaly) =
      (resolveWithJoker sec anomaly).restrict h := by
  by_cases hb : anomaly.is_broken <;> simp [resolveWithJoker, restrictAnomaly, hb]

theorem resolveWithJoker_idempotent {U V : GeometricOpenSet} (sec : SheafSection U)
    (anomaly : LocalAnomaly U) :
    resolveWithJoker (resolveWithJoker sec anomaly) anomaly = resolveWithJoker sec anomaly := by
  by_cases hb : anomaly.is_broken <;> simp [resolveWithJoker, hb]

noncomputable def propagateJoker {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : SheafSection.AmalgamationReady sU sV) : SheafSection (GeometricOpenSet.union U V) :=
  let base := SheafSection.constructGlobalSection sU sV h_ready
  if sU.val.morph_type = MorphismType.joker ∨ sV.val.morph_type = MorphismType.joker then
    { val := { base.val with morph_type := MorphismType.joker } }
  else base

theorem joker_absorption {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : SheafSection.AmalgamationReady sU sV)
    (hJ : sU.val.morph_type = MorphismType.joker ∨ sV.val.morph_type = MorphismType.joker) :
    (propagateJoker sU sV h_ready).val.morph_type = MorphismType.joker := by
  simp [propagateJoker, hJ]

theorem propagateJoker_symm {U V : GeometricOpenSet} (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : SheafSection.AmalgamationReady sU sV) :
    (propagateJoker sU sV h_ready).val.morph_type =
      (propagateJoker sV sU (SheafSection.amalgamationReady_symm sU sV h_ready)).val.morph_type := by
  simp [propagateJoker, or_comm]

theorem global_joker_extension {U V : GeometricOpenSet} (_f : U ⟶ V) (secU : SheafSection U)
    (_secV : SheafSection V) (anomalyU : LocalAnomaly U) :
    (resolveWithJoker secU anomalyU).val.morph_type = MorphismType.joker ∨
      (resolveWithJoker secU anomalyU).val.morph_type = secU.val.morph_type := by
  unfold resolveWithJoker; split_ifs <;> [left; right] <;> rfl

namespace Tests

example : GeometricOpenSet.overlap (⊤ : GeometricOpenSet) (⊥ : GeometricOpenSet) = (⊥ : GeometricOpenSet) := by simp [GeometricOpenSet.overlap]
example : GeometricOpenSet.union (⊤ : GeometricOpenSet) (⊥ : GeometricOpenSet) = (⊤ : GeometricOpenSet) := by simp [GeometricOpenSet.union]
example : Teramorphism.identity (⊤ : GeometricOpenSet) |>.morph_type = MorphismType.standard := by simp [Teramorphism.identity]

example :
    let t : Teramorphism (⊤ : GeometricOpenSet) (⊤ : GeometricOpenSet) :=
      { map := ContinuousMap.id (⊤ : GeometricOpenSet)
        morph_type := MorphismType.standard
        current_spin := SpinDirection.left
        is_valid := fun _ => Homeomorph.isHomeomorphism (Homeomorph.refl _) }
    (Teramorphism.spinLeftToRight t).current_spin = SpinDirection.right := by simp [Teramorphism.spinLeftToRight]

example :
    let sec : SheafSection (⊤ : GeometricOpenSet) := { val := Teramorphism.identity ⊤ }
    let h : (⊥ : GeometricOpenSet) ≤ (⊤ : GeometricOpenSet) := by simp
    (sec.restrict h).val.morph_type = MorphismType.standard := by simp [SheafSection.restrict]

example :
    let sec : SheafSection (⊤ : GeometricOpenSet) := { val := Teramorphism.identity ⊤ }
    (activateMotiveSheaf.app (Opposite.op (⊤ : GeometricOpenSet)) sec).val.current_spin = SpinDirection.right := by simp [activateMotiveSheaf]

example :
    let sec : SheafSection (⊤ : GeometricOpenSet) := { val := Teramorphism.identity ⊤ }
    let anomaly : LocalAnomaly (⊤ : GeometricOpenSet) := { is_broken := true }
    (resolveWithJoker sec anomaly).val.morph_type = MorphismType.joker := by simp [resolveWithJoker]

example (s : SpinDirection) : SpinDirection.toggle (SpinDirection.toggle s) = s :=
  SpinDirection.toggle_involution s

end Tests



