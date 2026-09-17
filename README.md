# ToposCheck-ToposCheck.lean
theorem twistedPresheaf_is_sheaf : Presheaf.IsSheaf (TwistedPresheaf Y) := by
  rw [Presheaf.isSheaf_iff_isSheafUniqueGlue]
  intro U ι U_cover h_cover s h_compat
  have h_cover_eq : Opposite.unop U = ⨆ i, U_cover i := by simpa using h_cover
  let sGlobal : (TwistedPresheaf Y).obj U := SheafSection.constructIndexedGlobalSection Y U_cover h_cover_eq s h_compat
  refine ⟨sGlobal, ?, ?⟩
  · intro i
    ext
    · apply ContinuousMap.ext; intro x
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection, SheafSection.restrict, glueContinuousMap]
      let j := (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose
      let hj := (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose_spec
      exact (SheafSection.compat_eval Y h_compat j i x.1 hj x.2).1
    · ext x
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection, SheafSection.restrict]
      let j := (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose
      let hj := (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose_spec
      exact (SheafSection.compat_eval Y h_compat j i x.1 hj x.2).2.1
    · ext x
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection, SheafSection.restrict]
      let j := (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose
      let hj := (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose_spec
      exact (SheafSection.compat_eval Y h_compat j i x.1 hj x.2).2.2.1
    · ext x
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection, SheafSection.restrict]
      let j := (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose
      let hj := (TopologicalSpace.Opens.mem_iSup.mp (by rwa [← h_cover_eq])).choose_spec
      exact (SheafSection.compat_eval Y h_compat j i x.1 hj x.2).2.2.2
  · intro s' h_match
    ext
    · apply ContinuousMap.ext; intro x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
      have h_eval := congr_arg (fun sec => sec.val.map ⟨x.1, hi⟩) (h_match i)
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection, glueContinuousMap]
      rw [← h_eval]
    · ext x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
      have h_eval := congr_arg (fun sec => sec.val.meta.morph_type ⟨x.1, hi⟩) (h_match i)
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [← h_eval]
    · ext x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
      have h_eval := congr_arg (fun sec => sec.val.meta.current_spin ⟨x.1, hi⟩) (h_match i)
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [← h_eval]
    · ext x
      have hx_cover : x.1 ∈ (⨆ i, U_cover i).1 := by rwa [← h_cover_eq]
      let i := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose
      let hi := (TopologicalSpace.Opens.mem_iSup.mp hx_cover).choose_spec
      have h_eval := congr_arg (fun sec => sec.val.meta.phase_shift ⟨x.1, hi⟩) (h_match i)
      dsimp [sGlobal, SheafSection.constructIndexedGlobalSection]
      rw [← h_eval]

noncomputable def TwistedSheaf : Sheaf (Opens.grothendieckTopology (TopCat.of AmbientSpace)) (Type u) :=
  ⟨TwistedPresheaf Y, by simpa [Presheaf.IsSheaf] using twistedPresheaf_is_sheaf Y⟩

