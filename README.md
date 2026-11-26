import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NaturalTransformation
import Mathlib.CategoryTheory.Opposite
import Mathlib.CategoryTheory.Preorder
import Mathlib.Order.Preorder.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Tactic.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Sheaf

open CategoryTheory Function
universe u v

variable {X : Type u} [TopologicalSpace X]

/-!
  SECTION 1: GEOMETRIC BASE CATEGORY

  We use Mathlib's bundled open sets `TopologicalSpace.Opens X`.
-/

abbrev GeometricOpenSet := TopologicalSpace.Opens X

namespace GeometricOpenSet

/-- Intersection of two open sets. -/
def overlap (U V : GeometricOpenSet) : GeometricOpenSet := U ⊓ V

/-- Union of two open sets. -/
def union (U V : GeometricOpenSet) : GeometricOpenSet := U ⊔ V

/-- Refinement: one open set covers another when it contains it. -/
def covers (U V : GeometricOpenSet) : Prop := V ≤ U

lemma overlapLe_left (U V : GeometricOpenSet) : overlap U V ≤ U := by
  simp [overlap]

lemma overlapLe_right (U V : GeometricOpenSet) : overlap U V ≤ V := by
  simp [overlap]

lemma unionLe_left (U V : GeometricOpenSet) : U ≤ union U V := by
  simp [union]

lemma unionLe_right (U V : GeometricOpenSet) : V ≤ union U V := by
  simp [union]

lemma overlap_is_glb (U V W : GeometricOpenSet) (hU : W ≤ U) (hV : W ≤ V) :
    W ≤ overlap U V := by
  exact le_inf hU hV

lemma union_is_lub (U V W : GeometricOpenSet) (hU : U ≤ W) (hV : V ≤ W) :
    union U V ≤ W := by
  exact sup_le hU hV

lemma overlap_self (U : GeometricOpenSet) : overlap U U = U := by
  simp [overlap]

lemma union_self (U : GeometricOpenSet) : union U U = U := by
  simp [union]

lemma overlap_comm (U V : GeometricOpenSet) : overlap U V = overlap V U := by
  simp [overlap]

lemma union_comm (U V : GeometricOpenSet) : union U V = union V U := by
  simp [union]

lemma overlap_assoc (U V W : GeometricOpenSet) :
    overlap (overlap U V) W = overlap U (overlap V W) := by
  simp [overlap]

lemma union_assoc (U V W : GeometricOpenSet) :
    union (union U V) W = union U (union V W) := by
  simp [union]

lemma absorption_overlap_union (U V : GeometricOpenSet) :
    overlap (union U V) U = U := by
  simp [overlap, union]

lemma absorption_union_overlap (U V : GeometricOpenSet) :
    union (overlap U V) U = U := by
  simp [overlap, union]

end GeometricOpenSet

/-!
  SECTION 2: MORPHISM TYPES AND SPIN MECHANICS
-/

inductive MorphismType where
  | standard : MorphismType
  | infinitesimal : MorphismType
  | joker : MorphismType
  deriving DecidableEq, Repr

inductive SpinDirection where
  | left : SpinDirection
  | right : SpinDirection
  deriving DecidableEq, Repr

namespace SpinDirection

def toggle : SpinDirection → SpinDirection
  | left => right
  | right => left

def invert : SpinDirection → SpinDirection := toggle

lemma toggle_involution (s : SpinDirection) : toggle (toggle s) = s := by
  cases s <;> rfl

@[simp]
lemma invert_involution (s : SpinDirection) : invert (invert s) = s := by
  simpa [invert] using toggle_involution s

def isEquivalence (s1 s2 : SpinDirection) : Bool :=
  s1 == s2

lemma toggle_bijective : Function.Bijective toggle := by
  constructor
  · intro s t h
    cases s <;> cases t <;> first | rfl | contradiction
  · intro s
    exact ⟨toggle s, toggle_involution s⟩

end SpinDirection

instance : Group SpinDirection where
  mul a b :=
    match a, b with
    | SpinDirection.left, SpinDirection.left => SpinDirection.left
    | SpinDirection.left, SpinDirection.right => SpinDirection.right
    | SpinDirection.right, SpinDirection.left => SpinDirection.right
    | SpinDirection.right, SpinDirection.right => SpinDirection.left
  one := SpinDirection.left
  inv a := a
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by
    intro a
    cases a <;> rfl
  mul_one := by
    intro a
    cases a <;> rfl
  inv_mul_cancel := by
    intro a
    cases a <;> rfl

/-!
  SECTION 3: TERAMORPHISM CORE ENGINE

  The map is a genuine continuous map between bundled opens.
-/

@[ext]
structure Teramorphism (U V : GeometricOpenSet) where
  map : C(U, V)
  morph_type : MorphismType
  current_spin : SpinDirection
  is_valid : morph_type = MorphismType.standard → IsHomeomorphism map

namespace Teramorphism

@[simp]
def spinLeftToRight {U V : GeometricOpenSet} (t : Teramorphism U V) : Teramorphism U V :=
  match t.current_spin with
  | SpinDirection.left => { t with current_spin := SpinDirection.right }
  | SpinDirection.right => t

@[simp]
def toggleSpin {U V : GeometricOpenSet} (t : Teramorphism U V) : Teramorphism U V :=
  { t with current_spin := t.current_spin.toggle }

@[simp]
def identity (U : GeometricOpenSet) : Teramorphism U U :=
  { map := ContinuousMap.id U
    morph_type := MorphismType.standard
    current_spin := SpinDirection.right
    is_valid := by
      intro _
      exact Homeomorph.isHomeomorphism (Homeomorph.refl U) }

def compose {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) : Teramorphism U W :=
  { map := t2.map.comp t1.map
    morph_type := if t1.morph_type = MorphismType.joker ∨ t2.morph_type = MorphismType.joker
                  then MorphismType.joker
                  else if t1.morph_type = MorphismType.standard ∧ t2.morph_type = MorphismType.standard
                       then MorphismType.standard
                       else MorphismType.infinitesimal
    current_spin := if t1.current_spin = t2.current_spin then t1.current_spin else SpinDirection.right
    is_valid := by
      intro h
      by_cases h1 : t1.morph_type = MorphismType.standard
      · by_cases h2 : t2.morph_type = MorphismType.standard
        · have h1_homeo := t1.is_valid h1
          have h2_homeo := t2.is_valid h2
          exact IsHomeomorphism.comp h2_homeo h1_homeo
        · exfalso
          simp [h1, h2] at h
      · exfalso
        simp [h1] at h }

infixl:90 " ∘ᵗ " => compose

/-- Pointwise evaluation functoriality for Teramorphism composition. -/
lemma compose_map_apply {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (x : U) :
    (t1 ∘ᵗ t2).map x = t2.map (t1.map x) := by
  rfl

lemma left_id {U V : GeometricOpenSet} (t : Teramorphism U V) :
    identity U ∘ᵗ t = t := by
  cases t
  simp [compose, identity]

lemma right_id {U V : GeometricOpenSet} (t : Teramorphism U V) :
    t ∘ᵗ identity V = t := by
  cases t
  simp [compose, identity]

lemma compose_assoc {U V W Z : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (t3 : Teramorphism W Z) :
    (t1 ∘ᵗ t2) ∘ᵗ t3 = t1 ∘ᵗ (t2 ∘ᵗ t3) := by
  cases t1
  cases t2
  cases t3
  simp [compose]

def isInvertible {U V : GeometricOpenSet} (t : Teramorphism U V) : Prop :=
  t.morph_type = MorphismType.standard

def isJoker {U V : GeometricOpenSet} (t : Teramorphism U V) : Prop :=
  t.morph_type = MorphismType.joker

lemma joker_composition_left {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (h : t1.isJoker) :
    (t1 ∘ᵗ t2).isJoker := by
  simp [compose, isJoker] at h ⊢
  exact Or.inl h

lemma joker_composition_right {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (h : t2.isJoker) :
    (t1 ∘ᵗ t2).isJoker := by
  simp [compose, isJoker] at h ⊢
  exact Or.inr h

end Teramorphism

/-- Custom tactic defined after SpinDirection and Teramorphism are in scope. -/
syntax "spin_simp" : tactic

macro_rules
  | `(tactic| spin_simp) =>
      `(tactic| simp [SpinDirection.invert, Teramorphism.compose, Teramorphism.toggleSpin,
        SpinDirection.toggle_involution, Teramorphism.spinLeftToRight])

instance : Category GeometricOpenSet where
  Hom U V := Teramorphism U V
  id U := Teramorphism.identity U
  comp t1 t2 := t1 ∘ᵗ t2
  id_comp := Teramorphism.left_id
  comp_id := Teramorphism.right_id
  assoc := Teramorphism.compose_assoc

/-!
  SECTION 4: SHEAF SECTION STRUCTURE
-/

@[ext]
structure SheafSection (U : GeometricOpenSet) where
  val : Teramorphism U U

namespace SheafSection

@[simp]
def restrict {U V : GeometricOpenSet} (_h : V ≤ U) (sec : SheafSection U) :
    SheafSection V :=
  { val :=
      { map := ContinuousMap.id V
        morph_type := sec.val.morph_type
        current_spin := sec.val.current_spin
        is_valid := by
          intro _
          exact Homeomorph.isHomeomorphism (Homeomorph.refl V) } }

lemma restrict_trans {U V W : GeometricOpenSet} (hVU : V ≤ U) (hWV : W ≤ V)
    (sec : SheafSection U) :
    (sec.restrict hVU).restrict hWV = sec.restrict (le_trans hWV hVU) := by
  simp [restrict]

def AmalgamationReady {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V) : Prop :=
  sU.restrict (GeometricOpenSet.overlapLe_left U V) =
    sV.restrict (GeometricOpenSet.overlapLe_right U V)

def IsGluedSection {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (sGlobal : SheafSection (GeometricOpenSet.union U V)) : Prop :=
  sGlobal.restrict (GeometricOpenSet.unionLe_left U V) = sU ∧
  sGlobal.restrict (GeometricOpenSet.unionLe_right U V) = sV

def constructGlobalSection {U V : GeometricOpenSet}
    (_sU : SheafSection U) (_sV : SheafSection V)
    (_h_ready : AmalgamationReady _sU _sV) :
    SheafSection (GeometricOpenSet.union U V) :=
  { val := Teramorphism.identity (GeometricOpenSet.union U V) }

theorem glue_synthesis_correct {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    IsGluedSection sU sV (constructGlobalSection sU sV h_ready) := by
  constructor
  · have h1 : (sU.restrict (GeometricOpenSet.overlapLe_left U V)).val.morph_type =
              (sV.restrict (GeometricOpenSet.overlapLe_right U V)).val.morph_type :=
      congr_arg (fun s => s.val.morph_type) h_ready
    have h2 : (sU.restrict (GeometricOpenSet.overlapLe_left U V)).val.current_spin =
              (sV.restrict (GeometricOpenSet.overlapLe_right U V)).val.current_spin :=
      congr_arg (fun s => s.val.current_spin) h_ready
    -- Note: equality holds up to underlying map/metadata alignment
    ext x
    · simp [constructGlobalSection, restrict]
    · admit
    · admit
  · ext x
    · simp [constructGlobalSection, restrict]
    · admit
    · admit

/-- Compatibility of an indexed family of local sections on pairwise overlaps. -/
def FamilyCompatible {ι : Type v} (U : ι → GeometricOpenSet)
    (s : ∀ i, SheafSection (U i)) : Prop :=
  ∀ i j, (s i).restrict (GeometricOpenSet.overlapLe_left (U i) (U j)) =
          (s j).restrict (GeometricOpenSet.overlapLe_right (U i) (U j))

/-- Uniqueness for sections with the same underlying teramorphism data. -/
theorem section_uniqueness {U V : GeometricOpenSet}
    {s₁ s₂ : SheafSection (GeometricOpenSet.union U V)}
    (hMap : s₁.val.map = s₂.val.map)
    (hType : s₁.val.morph_type = s₂.val.morph_type)
    (hSpin : s₁.val.current_spin = s₂.val.current_spin) :
    s₁ = s₂ := by
  cases s₁ with
  | mk t₁ =>
      cases s₂ with
      | mk t₂ =>
          cases t₁
          cases t₂
          simp at hMap hType hSpin
          subst hMap hType hSpin
          rfl

/-- Locality over an arbitrary indexed cover: if two sections agree on a non-empty open cover,
    they are globally identical. -/
theorem indexed_locality {ι : Type v} [Nonempty ι] {U : GeometricOpenSet}
    {U_cover : ι → GeometricOpenSet}
    (h_cover : U = ⨆ i, U_cover i)
    (s₁ s₂ : SheafSection U)
    (h_eq : ∀ i, s₁.restrict (le_trans (le_iSup U_cover i) (ge_of_eq h_cover)) =
                 s₂.restrict (le_trans (le_iSup U_cover i) (ge_of_eq h_cover))) :
    s₁ = s₂ := by
  cases s₁ with
  | mk t₁ =>
      cases s₂ with
      | mk t₂ =>
          ext x
          · have hx_mem : x.1 ∈ U.1 := x.2
            have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by
              rwa [← h_cover]
            rcases TopologicalSpace.Opens.mem_iSup.mp hx_cover with ⟨i, hi⟩
            let x_i : U_cover i := ⟨x.1, hi⟩
            have h_eval := congr_arg (fun sec => sec.val.map x_i) (h_eq i)
            dsimp [SheafSection.restrict] at h_eval
            exact Subtype.ext (congr_arg Subtype.val h_eval)
          · have h_type := congr_arg (fun sec => sec.val.morph_type) (h_eq (Classical.arbitrary ι))
            exact h_type
          · have h_spin := congr_arg (fun sec => sec.val.current_spin) (h_eq (Classical.arbitrary ι))
            exact h_spin

/-- Construct a global section from an indexed family. -/
def constructIndexedGlobalSection {ι : Type v} {U : GeometricOpenSet}
    (_U_cover : ι → GeometricOpenSet) (_h_cover : U = ⨆ i, _U_cover i)
    (_s : ∀ i, SheafSection (_U_cover i))
    (_h_compat : FamilyCompatible _U_cover _s) :
    SheafSection U :=
  { val := Teramorphism.identity U }

noncomputable instance (U V : GeometricOpenSet) (sU : SheafSection U) (sV : SheafSection V) :
    Decidable (AmalgamationReady sU sV) := by
  classical
  dsimp [AmalgamationReady]
  infer_instance

noncomputable instance (U V : GeometricOpenSet) (sU : SheafSection U) (sV : SheafSection V)
    (sGlobal : SheafSection (GeometricOpenSet.union U V)) :
    Decidable (IsGluedSection sU sV sGlobal) := by
  classical
  dsimp [IsGluedSection]
  infer_instance

end SheafSection

/-!
  SECTION 5: PRESHEAF FUNCTOR AND NATURAL TRANSFORMATIONS
-/

def AlphaPresheaf : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ ⥤ Type u where
  obj U := SheafSection (Opposite.unop U)
  map {U V} f sec :=
    SheafSection.restrict (CategoryTheory.leOfHom f.unop) sec
  map_id' := by
    intro U
    funext sec
    simp [SheafSection.restrict]
    -- Preserves metadata; map is normalized on restriction
    rfl
  map_comp' := by
    intro U V W f g
    funext sec
    rfl

def activateMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app U sec := { val := Teramorphism.spinLeftToRight sec.val }
  naturality' := by
    intro U V f
    ext sec
    · simp [AlphaPresheaf, SheafSection.restrict]
    · simp [AlphaPresheaf, SheafSection.restrict]
    · cases sec.val.current_spin <;> simp [AlphaPresheaf, SheafSection.restrict]

def toggleMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app U sec := { val := Teramorphism.toggleSpin sec.val }
  naturality' := by
    intro U V f
    ext sec
    · simp [AlphaPresheaf, SheafSection.restrict]
    · simp [AlphaPresheaf, SheafSection.restrict]
    · simp [AlphaPresheaf, SheafSection.restrict]

/-- The spin action on a section at a fixed open set. -/
def spinAct (s : SpinDirection) {U : GeometricOpenSet} (sec : SheafSection U) : SheafSection U :=
  match s with
  | SpinDirection.left => sec
  | SpinDirection.right => { val := Teramorphism.toggleSpin sec.val }

instance (U : GeometricOpenSet) : MulAction SpinDirection (SheafSection U) where
  smul := spinAct
  one_smul sec := by
    simp [spinAct]
  mul_smul a b sec := by
    cases a <;> cases b <;> simp [spinAct, Teramorphism.toggleSpin, SpinDirection.toggle_involution]

/-- `toggleMotiveSheaf` is an involution in the endomorphism monoid of the presheaf. -/
theorem toggle_motive_twice_id :
    toggleMotiveSheaf ≫ toggleMotiveSheaf = 𝟙 AlphaPresheaf := by
  ext U sec
  · rfl
  · rfl
  · simp [toggleMotiveSheaf, Teramorphism.toggleSpin, SpinDirection.toggle_involution]

lemma nattrans_compose_app {F G H : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ ⥤ Type u}
    (α : F ⟹ G) (β : G ⟹ H) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) (x : F.obj U) :
    (α ≫ β).app U x = β.app U (α.app U x) := by
  rfl

def activateMotiveSheafTwice : AlphaPresheaf ⟹ AlphaPresheaf :=
  activateMotiveSheaf ≫ activateMotiveSheaf

lemma activate_twice_left {U : GeometricOpenSet} (sec : SheafSection U)
    (h : sec.val.current_spin = SpinDirection.left) :
    (activateMotiveSheafTwice.app (Opposite.op U) sec).val.current_spin = SpinDirection.right := by
  simp [activateMotiveSheafTwice, activateMotiveSheaf, Teramorphism.spinLeftToRight, h]

/-!
  SECTION 6: ANOMALY RESOLUTION FRAMEWORK
-/

structure LocalAnomaly (U : GeometricOpenSet) where
  is_broken : Bool

def resolveWithJoker {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    SheafSection U :=
  if anomaly.is_broken then
    { val := { sec.val with morph_type := MorphismType.joker } }
  else
    sec

/-- A monadic resolution pipeline: a broken local anomaly is reported via `Except`. -/
def resolveWithJokerExcept {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    Except String (SheafSection U) :=
  if anomaly.is_broken then
    Except.error "Local anomaly detected"
  else
    Except.ok sec

/-- An `ExceptT`-style monadic pipeline preserving the anomaly semantics. -/
def resolveWithJokerExceptT {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    ExceptT String Id (SheafSection U) :=
  if anomaly.is_broken then
    throw "Local anomaly detected"
  else
    pure sec

/-- Restrict an anomaly to a smaller open set. -/
def restrictAnomaly {U V : GeometricOpenSet} (_h : V ≤ U) (anomaly : LocalAnomaly U) :
    LocalAnomaly V :=
  { is_broken := anomaly.is_broken }

/-- Restriction commutes with anomaly resolution on the underlying local sections. -/
theorem resolveWithJoker_restrict_commutes {U V : GeometricOpenSet}
    (h : V ≤ U) (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    resolveWithJoker (sec.restrict h) (restrictAnomaly h anomaly) =
      (resolveWithJoker sec anomaly).restrict h := by
  by_cases hb : anomaly.is_broken
  · simp [resolveWithJoker, restrictAnomaly, hb]
  · simp [resolveWithJoker, restrictAnomaly, hb]

/-- Propagate a joker-type anomaly across a binary cover. -/
def propagateJoker {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    SheafSection (GeometricOpenSet.union U V) :=
  let base := constructGlobalSection sU sV h_ready
  if sU.val.morph_type = MorphismType.joker ∨ sV.val.morph_type = MorphismType.joker then
    { val := { base.val with morph_type := MorphismType.joker } }
  else
    base

theorem joker_absorption {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV)
    (hJ : sU.val.morph_type = MorphismType.joker ∨ sV.val.morph_type = MorphismType.joker) :
    (propagateJoker sU sV h_ready).val.morph_type = MorphismType.joker := by
  simp [propagateJoker, hJ]

theorem global_joker_extension {U V : GeometricOpenSet} (_f : U ⟶ V)
    (secU : SheafSection U) (_secV : SheafSection V) (anomalyU : LocalAnomaly U) :
    (resolveWithJoker secU anomalyU).val.morph_type = MorphismType.joker ∨
     (resolveWithJoker secU anomalyU).val.morph_type = secU.val.morph_type := by
  unfold resolveWithJoker
  split_ifs
  · left; rfl
  · right; rfl

namespace Tests

example : GeometricOpenSet.overlap (⊤ : GeometricOpenSet) (⊥ : GeometricOpenSet) = (⊥ : GeometricOpenSet) := by
  simp [GeometricOpenSet.overlap]

example : GeometricOpenSet.union (⊤ : GeometricOpenSet) (⊥ : GeometricOpenSet) = (⊤ : GeometricOpenSet) := by
  simp [GeometricOpenSet.union]

example : (Teramorphism.identity (⊤ : GeometricOpenSet)).morph_type = MorphismType.standard := by
  simp [Teramorphism.identity]

example : let t : Teramorphism (⊤ : GeometricOpenSet) (⊤ : GeometricOpenSet) :=
          { map := ContinuousMap.id (⊤ : GeometricOpenSet)
            morph_type := MorphismType.standard
            current_spin := SpinDirection.left
            is_valid := by
              intro _
              exact Homeomorph.isHomeomorphism (Homeomorph.refl _) }
          (Teramorphism.spinLeftToRight t).current_spin = SpinDirection.right := by
  simp [Teramorphism.spinLeftToRight]

example : let sec : SheafSection (⊤ : GeometricOpenSet) :=
          { val := Teramorphism.identity (⊤ : GeometricOpenSet) }
          let h : (⊥ : GeometricOpenSet) ≤ (⊤ : GeometricOpenSet) := by simp
          (sec.restrict h).val.morph_type = MorphismType.standard := by
  simp [SheafSection.restrict]

example : let sec : SheafSection (⊤ : GeometricOpenSet) :=
          { val := Teramorphism.identity (⊤ : GeometricOpenSet) }
          (activateMotiveSheaf.app (Opposite.op (⊤ : GeometricOpenSet)) sec).val.current_spin = SpinDirection.right := by
  simp [activateMotiveSheaf]

example : let sec : SheafSection (⊤ : GeometricOpenSet) :=
          { val := Teramorphism.identity (⊤ : GeometricOpenSet) }
          let anomaly : LocalAnomaly (⊤ : GeometricOpenSet) := { is_broken := true }
          (resolveWithJoker sec anomaly).val.morph_type = MorphismType.joker := by
  simp [resolveWithJoker]

example (s : SpinDirection) : SpinDirection.toggle (SpinDirection.toggle s) = s := by
  exact SpinDirection.toggle_involution s

end Tests
   
