import algebraic_topology.simplex_category
import set_theory.cardinal

open category_theory
namespace simplex_category
open_locale simplicial


-- instance split_epi_comp {k n m : ℕ} (f : [k] ⟶ [n]) [hf : split_epi f] (g : [n] ⟶ [m]) [hg : split_epi g] :
-- split_epi (f ≫ g) :=
-- begin
--   refine ⟨section_ g ≫ section_ f, _⟩,
-- end

/- Degeneracy maps are compositions of σ maps. -/

instance σ_split_epi {n} (i : fin (n+1)) : split_epi (σ i) := ⟨δ i.cast_succ, δ_comp_σ_self⟩

class inductive degeneracy {n : ℕ} : Π {m : ℕ}, ([m] ⟶ [n]) → Sort*
| id                          : @degeneracy n (𝟙 [n])
| comp {k} (g: [k] ⟶ [n]) (i) : @degeneracy k g → @degeneracy (k+1) (σ i ≫ g)

lemma le_of_degeneracy {n : ℕ} : Π {m : ℕ} (s : [m] ⟶ [n]) (hs : degeneracy s), n ≤ m
| n s degeneracy.id            := le_refl n
| m s (degeneracy.comp g i hg) := nat.le_succ_of_le (le_of_degeneracy g hg)

lemma degeneracy_comp_degeneracy {m n : ℕ} {f : [m] ⟶ [n]} (hf : degeneracy f) :
Π {l : ℕ} {g : [l] ⟶ [m]} (hg : degeneracy g), degeneracy (g ≫ f)
| m g degeneracy.id            := begin rw category.id_comp, exact hf, end
| l s (degeneracy.comp g i hg) :=
begin
  rw category.assoc (σ i) g f,
  exact degeneracy.comp _ _ (degeneracy_comp_degeneracy hg),
end

lemma split_epi_of_degeneracy {n : ℕ} : Π {m} {f : [m] ⟶ [n]} (hf : degeneracy f), split_epi f
| n f degeneracy.id            := ⟨𝟙 [n], category.id_comp (𝟙 [n])⟩
| m f (degeneracy.comp g i hg) :=
begin
  rcases split_epi_of_degeneracy hg with ⟨g_ret, g_comp⟩,
  rcases (infer_instance : split_epi (σ i)) with ⟨σ_ret, σ_comp⟩,
  refine ⟨g_ret ≫ σ_ret, _⟩,
  simp only [auto_param_eq] at *,
  rw [category.assoc, ←category.assoc σ_ret (σ i) g, σ_comp, category.id_comp, g_comp],
end


/- Face maps are compositions of δ maps. -/

instance δ_split_mono {n} (i : fin (n+2)) : split_mono (δ i) :=
begin
  by_cases hi : i < fin.last (n+1),
  { rw ←fin.cast_succ_cast_pred hi,
    exact ⟨σ i.cast_pred, δ_comp_σ_self⟩,},
  { push_neg at hi,
    have hi' : i ≠ 0, from ne_of_gt (gt_of_ge_of_gt hi fin.last_pos),
    rw ←fin.succ_pred i hi',
    exact ⟨σ (i.pred hi'), δ_comp_σ_succ⟩,},
end

class inductive face {n : ℕ} : Π {m : ℕ}, ([n] ⟶ [m]) → Sort*
| id                          : @face n (𝟙 [n])
| comp {m} (g: [n] ⟶ [m]) (i) : @face m g → @face (m+1) (g ≫ δ i)

lemma le_of_face {n : ℕ} : Π {m : ℕ} (s : [n] ⟶ [m]) (hs : face s), n ≤ m
| n s face.id            := le_refl n
| m s (face.comp g i hg) := nat.le_succ_of_le (le_of_face g hg)

lemma face_comp_face {l m : ℕ} {g : [l] ⟶ [m]} (hg : face g) :
Π {n : ℕ} {f : [m] ⟶ [n]} (hf : face f), face (g ≫ f)
| m f face.id            := begin rw category.comp_id, exact hg, end
| n s (face.comp f i hf) :=
begin
  rw ←category.assoc g f (δ i),
  exact face.comp _ _ (face_comp_face hf),
end

lemma split_mono_of_face {n : ℕ} : Π {m} {f : [n] ⟶ [m]} (hf : face f), split_mono f
| n f face.id            := ⟨𝟙 [n], category.id_comp (𝟙 [n])⟩
| m f (face.comp g i hg) :=
begin
  rcases split_mono_of_face hg with ⟨g_ret, g_comp⟩,
  rcases (infer_instance : split_mono (δ i)) with ⟨δ_ret, δ_comp⟩,
  refine ⟨δ_ret ≫ g_ret, _⟩,
  simp only [auto_param_eq] at *,
  rw [category.assoc, ←category.assoc (δ i) δ_ret g_ret, δ_comp, category.id_comp, g_comp],
end



/-- An isomorphism has same domain and codomain. -/
lemma auto_of_iso {n m} (f : [n] ⟶ [m]) [hf : is_iso f] : m = n :=
begin
  have h1 : fin(n+1) ≃ fin(m+1),
  { refine ⟨f.to_preorder_hom , (inv f).to_preorder_hom, _, _⟩,
    dsimp only [function.left_inverse],
    { intro i,
      suffices h : hom.to_preorder_hom (f ≫ inv f) i = i, simp at h, exact h,
      rw [is_iso.hom_inv_id], simp, },
    { intro i,
      suffices h : hom.to_preorder_hom (inv f ≫ f) i = i, simp at h, exact h,
      rw [is_iso.inv_hom_id], simp, }},
  suffices h : cardinal.mk (fin (n + 1)) = cardinal.mk (fin (m + 1)),
  { rw [cardinal.mk_fin, cardinal.mk_fin] at h,
    norm_cast at h,
    exact (nat.succ.inj h).symm, },
  exact cardinal.eq_congr h1,
end

lemma id_le_iso {n} (f : [n] ⟶ [n]) [is_iso f] :  ∀ i, i ≤ f.to_preorder_hom i :=
begin
  let func     := f.to_preorder_hom,
  let func_inv := (inv f).to_preorder_hom,
  intro i, apply i.induction_on, exact fin.zero_le _,
  intros j Hj,
  rw [←not_lt, ←fin.le_cast_succ_iff, not_le],
  suffices h : func  j.cast_succ ≠ func j.succ,
  exact gt_of_gt_of_ge (lt_of_le_of_ne (func.monotone (le_of_lt (fin.cast_succ_lt_succ j))) h) Hj,
  intro h,
  apply (lt_self_iff_false j.succ).mp,
  suffices h' : j.succ = j.cast_succ,
  calc j.succ = j.cast_succ : h'
          ... < j.succ : fin.cast_succ_lt_succ j,
  suffices h' : (f ≫ inv f).to_preorder_hom j.succ = (f ≫ inv f).to_preorder_hom j.cast_succ,
  rw [is_iso.hom_inv_id f] at h', simp at h', exact h',
  simp,
  exact congr_arg func_inv h.symm,
end

/-- Only automorphism is the identity. -/
lemma id_of_iso {n} (f : [n] ⟶ [n]) [is_iso f] : f = 𝟙 [n] :=
begin
  let func     := f.to_preorder_hom,
  let func_inv := (inv f).to_preorder_hom,
  have h₁ : ∀ i, i ≤ f.to_preorder_hom i, from id_le_iso f,
  have h₂ : ∀ i, i ≤ (inv f).to_preorder_hom i, from id_le_iso (inv f),
  ext1, ext1 i, simp,
  suffices h : func i ≤ (inv f ≫ f).to_preorder_hom i,
  { rw [is_iso.inv_hom_id f] at h, simp at h, from le_antisymm h (h₁ i), },
  simp,
  exact func.monotone (h₂ i),
end

-- /-- An isomorphism is a degeneracy. -/
-- lemma degeneracy_of_iso {n m} (f : [n] ⟶ [m]) [hf : is_iso f] : degeneracy f :=
-- begin
--   let g := inv f,
--   have hfg : f ≫ g = 𝟙 [n], from is_iso.hom_inv_id f,
--   have hgf : g ≫ f = 𝟙 [m], from is_iso.inv_hom_id f,
--   have hnm : m = n, from auto_of_iso f,
--   rw hnm at *,
--   -- rw hnm at g,
--   sorry,
--   -- have hf : f = 𝟙 [n], from @id_of_iso _ f hf,
-- end

-- /-- An isomorphism is a face map. -/
-- lemma face_of_iso {n m} (f : [n] ⟶ [m]) [is_iso f] : face f := sorry


/-- A degenerate automorphism is an isomorphism. -/
lemma iso_of_degeneracy_auto {n} : Π {m} (f : [m] ⟶ [n]), degeneracy f → n = m → is_iso f
| n f degeneracy.id h            := is_iso.id [n]
| m f (degeneracy.comp g i hg) h :=
  false.rec _ ((lt_self_iff_false n).mp (lt_of_lt_of_le
    (nat.lt_succ_of_le (le_of_degeneracy g hg)) (le_of_eq h.symm)))

/-- A degenerate automorphism is an isomorphism. -/
lemma iso_of_face_auto {n} : Π {m} (f : [n] ⟶ [m]), face f → n = m → is_iso f
| n f face.id h            := is_iso.id [n]
| m f (face.comp g i hg) h :=
  false.rec _ ((lt_self_iff_false n).mp (lt_of_lt_of_le
    (nat.lt_succ_of_le (le_of_face g hg)) (le_of_eq h.symm)))


def inj {n m} (f : [n] ⟶ [m]) := function.injective f.to_preorder_hom

lemma face_of_injective {n m} (f : [n] ⟶ [m]) (hf : inj f) : face f :=
begin
  sorry
end

-- /-- [0] is terminal in the simplex category. -/
-- lemma : limits.is_terminal [0] := limits.is_terminal.of_unique

-- lemma cast_succ_le_cast_succ_iff {n} {a b : fin n} :
--   a.cast_succ ≤ b.cast_succ ↔ a ≤ b :=
-- by rw [←not_lt, ←not_lt, fin.cast_succ_lt_cast_succ_iff]

/-- If f(i) = f(i+1) then σ i ≫ δ i+1 ≫ f = f -/
lemma σ_comp_δ_comp {n m} (f: [n + 1] ⟶ [m]) (i : fin (n + 1))
(H : f.to_preorder_hom i.cast_succ = f.to_preorder_hom i.succ) :
  σ i ≫ δ i.succ ≫ f = f :=
begin
  ext1, ext1 j,
  dsimp [δ, fin.succ_above, σ],
  simp, dsimp [fin.pred_above],
  split_ifs,
  { have hjpred : j ≠ 0, from fin.pred_above._proof_1 i j h,
    have hj : j = i.succ,
    { apply le_antisymm,
      { rwa [←not_le, fin.le_cast_succ_iff, fin.succ_pred, not_lt] at h_1, },
      { rwa [←not_le, fin.le_cast_succ_iff, not_lt] at h, }},
    have hi : j.pred hjpred = i, rwa [←fin.succ_inj, fin.succ_pred],
    rwa [hi, hj], },
  { rw j.succ_pred,},
  { rw fin.cast_succ_cast_lt, },
  { rw ←fin.le_cast_succ_iff at h_1, finish,}
end

/-- Every map has a decompostion into a degeneracy and a face map. -/
theorem decomp_degeneracy_face {n m} (f : [n] ⟶ [m]) :
  ∃ {k} (s : [n] ⟶ [k]) [degeneracy s] (d : [k] ⟶ [m]) [face d], f = s ≫ d :=
begin
  induction n with n ih_n, { induction m with m ih_m,
  { refine ⟨0, 𝟙 [0], degeneracy.id, 𝟙 [0], face.id, sorry⟩, },
  { have hf : inj f,
    { dsimp[inj, function.injective],
      intros i j hij, finish, },
    exact ⟨0, 𝟙 [0], degeneracy.id, f, face_of_injective f hf, (category.id_comp f).symm⟩,}},
  { by_cases hf : function.injective f.to_preorder_hom,
    exact ⟨n.succ, 𝟙 [n.succ], degeneracy.id, f, face_of_injective f hf, (category.id_comp f).symm⟩,
    push_neg at hf,
    rcases hf with ⟨j₁, j₂, hfj, hj⟩,
    wlog j₁lj₂ : j₁ < j₂ := ne.lt_or_lt hj using j₁ j₂,
    let i := j₁.cast_pred,
    have hi : f.to_preorder_hom i.cast_succ = f.to_preorder_hom i.succ, sorry,
    clear j₁lj₂ hfj hj j₂,
    let g := δ i.succ ≫ f,
    specialize ih_n g,
    rcases ih_n with ⟨k, s, hs, d, hd, hsd⟩,
    refine ⟨k, σ i ≫ s, degeneracy.comp s i hs, d, hd, _⟩,
    rw [category.assoc, ←hsd],
    apply symm,
    exact σ_comp_δ_comp f i hi, }
end

-- /-- Every map has a decompostion into a degeneracy and a face map. -/
-- theorem decomp_degeneracy_face : Π {n m} (f : [n] ⟶ [m]),
--   ∃ {k} (s : [n] ⟶ [k]) [degeneracy s] (d : [k] ⟶ [m]) [face d], f = s ≫ d
-- | 0 0     f := ⟨0, 𝟙 [0], degeneracy.id, 𝟙 [0], face.id, sorry⟩
-- | 0 (m+1) f := ⟨0, 𝟙 [0], degeneracy.id, f, face_of_injective f sorry, (category.id_comp f).symm⟩
-- | (n+1) m f :=
-- begin
--   by_cases hf : function.injective f.to_preorder_hom,
--   exact ⟨n.succ, 𝟙 [n.succ], degeneracy.id, f, face_of_injective f hf, (category.id_comp f).symm⟩,
--   push_neg at hf,
--   rcases hf with ⟨j₁, j₂, hfj, hj⟩,
--   wlog j₁lj₂ : j₁ < j₂ := ne.lt_or_lt hj using j₁ j₂,
--   let i := j₁.cast_pred,
--   have hi : f.to_preorder_hom i.cast_succ = f.to_preorder_hom i.succ, sorry,
--   clear j₁lj₂ hfj hj j₂,
--   let g := δ i.succ ≫ f,
--   -- specialize decomp_degeneracy_face g,
--   rcases decomp_degeneracy_face g with ⟨k, s, hs, d, hd, hsd⟩,
--   refine ⟨k, σ i ≫ s, degeneracy.comp s i hs, d, hd, _⟩,
--   rw [category.assoc, ←hsd],
--   apply symm,
--   exact σ_comp_δ_comp f i hi,
-- end

theorem eq_of_same_sections {n m} (s₁ s₂ : [n] ⟶ [m]) [degeneracy s₁] [degeneracy s₂] :
(∀ (f : [m] ⟶ [n]), f ≫ s₁ = 𝟙 [m] ↔ f ≫ s₂ = 𝟙 [m]) → s₁ = s₂ := sorry

end simplex_category
