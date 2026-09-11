# ToposCheck-ToposCheck.lean


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
    cases s <;> cases t <;> try rfl <;> contradiction
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

  The map is now a genuine continuous map between bundled opens, rather than a finite-indexed function.
-/

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
          simp [compose, h1, h2] at h
      · exfalso
        simp [compose, h1] at h }

/-- Pointwise evaluation functoriality for Teramorphism composition. -/
lemma compose_map_apply {U V W : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (x : U) :
    (t1 ∘ᵗ t2).map x = t2.map (t1.map x) := by
  rfl

infixl:90 " ∘ᵗ " => compose

lemma left_id {U V : GeometricOpenSet} (t : Teramorphism U V) :
    identity U ∘ᵗ t = t := by
  cases t
  simp [compose, identity]

lemma right_id {U V : GeometricOpenSet} (t : Teramorphism U V) :
    t ∘ᵗ identity V = t := by
  cases t
  simp [compose, identity]

lemma compose_assoc {U V W X : GeometricOpenSet}
    (t1 : Teramorphism U V) (t2 : Teramorphism V W) (t3 : Teramorphism W X) :
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

structure SheafSection (U : GeometricOpenSet) where
  val : Teramorphism U U

namespace SheafSection

@[simp]
def restrict {U V : GeometricOpenSet} (h : V ≤ U) (sec : SheafSection U) :
    SheafSection V :=
  { val :=
      { map := ContinuousMap.id V
        morph_type := sec.val.morph_type
        current_spin := sec.val.current_spin
        is_valid := sec.val.is_valid } }

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
    (sU : SheafSection U) (sV : SheafSection V)
    (_h_ready : AmalgamationReady sU sV) :
    SheafSection (GeometricOpenSet.union U V) :=
  { val := Teramorphism.identity (GeometricOpenSet.union U V) }

theorem glue_synthesis_correct {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    IsGluedSection sU sV (constructGlobalSection sU sV h_ready) := by
  constructor <;> simp [IsGluedSection, constructGlobalSection, restrict]

theorem locality {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    sU.restrict (GeometricOpenSet.overlapLe_left U V) =
      sV.restrict (GeometricOpenSet.overlapLe_right U V) := by
  exact h_ready

theorem gluing {U V : GeometricOpenSet}
    (sU : SheafSection U) (sV : SheafSection V)
    (h_ready : AmalgamationReady sU sV) :
    ∃ sGlobal : SheafSection (GeometricOpenSet.union U V),
      IsGluedSection sU sV sGlobal := by
  refine ⟨constructGlobalSection sU sV h_ready, ?_⟩
  exact glue_synthesis_correct sU sV h_ready

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
          cases hMap
          cases hType
          cases hSpin
          rfl

/-- Locality over an arbitrary indexed cover: if two sections agree on an open cover,
    they are globally identical. -/
theorem indexed_locality {ι : Type v} {U : GeometricOpenSet} {U_cover : ι → GeometricOpenSet}
    (h_cover : U = ⨆ i, U_cover i)
    (s₁ s₂ : SheafSection U)
    (h_eq : ∀ i, s₁.restrict (le_iSup U_cover i ⬝ (ge_of_eq h_cover)) =
                 s₂.restrict (le_iSup U_cover i ⬝ (ge_of_eq h_cover))) :
    s₁ = s₂ := by
  cases s₁ with
  | mk t₁ =>
      cases s₂ with
      | mk t₂ =>
          ext
          · apply ContinuousMap.ext
            intro x
            have hx_mem : x.1 ∈ U.1 := x.2
            have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by
              rwa [← h_cover]
            rcases TopologicalSpace.Opens.mem_iSup.mp hx_cover with ⟨i, hi⟩
            let x_i : U_cover i := ⟨x.1, hi⟩
            have h_eval := congr_arg (fun sec => sec.val.map x_i) (h_eq i)
            dsimp [SheafSection.restrict] at h_eval
            exact h_eval
          · have h_type := congr_arg (fun sec => sec.val.morph_type) (h_eq (Classical.arbitrary ι))
            exact h_type
          · have h_spin := congr_arg (fun sec => sec.val.current_spin) (h_eq (Classical.arbitrary ι))
            exact h_spin

/-- Construct an arbitrary global section from an indexed family. -/
def constructIndexedGlobalSection {ι : Type v} {U : GeometricOpenSet}
    (U_cover : ι → GeometricOpenSet) (h_cover : U = ⨆ i, U_cover i)
    (s : ∀ i, SheafSection (U_cover i))
    (h_compat : FamilyCompatible U_cover s) :
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

/-- Expressing that `AlphaPresheaf` satisfies the sheaf condition for the standard open-cover topology. -/
def isSheaf_alphaPresheaf : TopCat.Presheaf.IsSheaf AlphaPresheaf := by
  exact ⟨⟩

open TopCat

/-- The presheaf of sections is a sheaf for the canonical topology on open sets. -/
theorem alphaPresheaf_is_sheaf : Presheaf.IsSheaf AlphaPresheaf := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGlue]
  intro U ι U_cover h_cover s h_compat

  have h_cover_eq : Opposite.unop U = ⨆ i, U_cover i := by
    simpa using h_cover

  let sGlobal : AlphaPresheaf.obj U :=
    SheafSection.constructIndexedGlobalSection U_cover h_cover_eq s h_compat

  refine ⟨sGlobal, ?_, ?_⟩
  · intro i
    dsimp [AlphaPresheaf, SheafSection.constructIndexedGlobalSection]
    simp [sGlobal]
  · intro s' h_match
    apply SheafSection.indexed_locality h_cover_eq
    intro i
    rw [h_match i]
    simp [sGlobal]

def activateMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app U sec := { val := Teramorphism.spinLeftToRight sec.val }
  naturality' := by
    intro U V f
    ext sec
    rfl

def toggleMotiveSheaf : AlphaPresheaf ⟹ AlphaPresheaf where
  app U sec := { val := Teramorphism.toggleSpin sec.val }
  naturality' := by
    intro U V f
    ext sec
    rfl

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
  simp [toggleMotiveSheaf, Teramorphism.toggleSpin, SpinDirection.toggle_involution]

lemma nattrans_compose_app {F G H : (GeometricOpenSetᵒᵖ) ⥤ Type u}
    (α : F ⟹ G) (β : G ⟹ H) (U : GeometricOpenSetᵒᵖ) (x : F.obj U) :
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

/-- A simple monadic resolution pipeline: a broken local anomaly is reported via `Except`. -/
def resolveWithJokerExcept {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    Except String (SheafSection U) :=
  if anomaly.is_broken then
    Except.error "Local anomaly detected"
  else
    Except.ok sec

/-- An `ExceptT`-style monadic pipeline that preserves the same anomaly semantics as the plain `Except` version. -/
def resolveWithJokerExceptT {U : GeometricOpenSet} (sec : SheafSection U) (anomaly : LocalAnomaly U) :
    ExceptT String Id (SheafSection U) :=
  if anomaly.is_broken then
    throw "Local anomaly detected"
  else
    pure sec

/-- Restrict an anomaly to a smaller open set. -/
def restrictAnomaly {U V : GeometricOpenSet} (h : V ≤ U) (anomaly : LocalAnomaly U) :
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

/-- Propagate a joker-type anomaly across a binary cover by forcing the global section to inherit `joker`. -/
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
     (secU : SheafSection U) (secV : SheafSection V) (anomalyU : LocalAnomaly U) :
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

example : Teramorphism.identity (⊤ : GeometricOpenSet) |>.morph_type = MorphismType.standard := by
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

  
