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
class inductive degeneracy {n : ℕ} : Π {m : ℕ}, ([m] ⟶ [n]) → Sort*
| id                          : degeneracy (𝟙 [n])
| comp {k} (g: [k] ⟶ [n]) (i) : degeneracy g → degeneracy (σ i ≫ g)

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

instance σ_split_epi {n} (i : fin (n+1)) : split_epi (σ i) := ⟨δ i.cast_succ, δ_comp_σ_self⟩

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
class inductive face {n : ℕ} : Π {m : ℕ}, ([n] ⟶ [m]) → Sort*
| id                          : face (𝟙 [n])
| comp {m} (g: [n] ⟶ [m]) (i) : face g → face (g ≫ δ i)

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

/-- A bijective morphism is an isomorphism. -/
lemma iso_of_bijective {n m} (f : [n] ⟶ [m]) (hf : function.bijective f.to_preorder_hom) :
is_iso f :=
begin
  split,
  have hjinj := hf.1,
  rw function.bijective_iff_has_inverse at hf,
  rcases hf with ⟨g, hfg, hgf⟩,
  refine ⟨mk_hom ⟨g,_⟩, _⟩,
  {
    intros i j hij,
    rw le_iff_eq_or_lt at hij,
    cases hij with hij hij, rwa hij,
    by_contra hgij,
    push_neg at hgij,
    let H := f.to_preorder_hom.monotone (le_of_lt hgij),
    rw [hgf, hgf, ←not_lt] at H,
    exact H hij,
  },
  { split,
    ext1, ext1 i, simp,
    exact hfg i,
    ext1, ext1 i, simp,
    exact hgf i, }
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
  have h : cardinal.mk (fin (n + 1)) = cardinal.mk (fin (m + 1)), from cardinal.eq_congr h1,
  rw [cardinal.mk_fin, cardinal.mk_fin] at h,
  norm_cast at h,
  exact (nat.succ.inj h).symm,
end

lemma id_le_iso {n} (f : [n] ⟶ [n]) [is_iso f] : ∀ i, i ≤ f.to_preorder_hom i :=
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
lemma id_of_auto {n} (f : [n] ⟶ [n]) [is_iso f] : f = 𝟙 [n] :=
begin
  let func     := f.to_preorder_hom,
  let func_inv := (inv f).to_preorder_hom,
  ext1, apply le_antisymm,
  { have h : func.comp preorder_hom.id ≤ func.comp func_inv,
    from λ i, func.monotone (id_le_iso (inv f) i),
    change func ≤ (inv f ≫ f).to_preorder_hom at h,
    rw [is_iso.inv_hom_id f] at h,
    simpa using h,},
  { exact id_le_iso f, }
end

/-- An isomorphism is a degeneracy. -/
instance degeneracy_of_iso {n m} (f : [n] ⟶ [m]) [hf : is_iso f] : degeneracy f :=
begin
  tactic.unfreeze_local_instances,
  cases auto_of_iso f,
  rw @id_of_auto n f hf,
  exact degeneracy.id,
end

/-- An isomorphism is a face map. -/
lemma face_of_iso {n m} (f : [n] ⟶ [m]) [hf : is_iso f] : face f :=
begin
  tactic.unfreeze_local_instances,
  cases auto_of_iso f,
  rw @id_of_auto n f hf,
  exact face.id,
end

/-- A degenerate automorphism is an isomorphism. -/
lemma iso_of_degeneracy_auto {n} : Π {m} (f : [m] ⟶ [n]), degeneracy f → n = m → is_iso f
| n f degeneracy.id h            := is_iso.id [n]
| m f (degeneracy.comp g i hg) h :=
  false.rec _ ((lt_self_iff_false n).mp (lt_of_lt_of_le
    (nat.lt_succ_of_le (le_of_degeneracy g hg)) (le_of_eq h.symm)))

/-- A face automorphism is an isomorphism. -/
lemma iso_of_face_auto {n} : Π {m} (f : [n] ⟶ [m]), face f → n = m → is_iso f
| n f face.id h            := is_iso.id [n]
| m f (face.comp g i hg) h :=
  false.rec _ ((lt_self_iff_false n).mp (lt_of_lt_of_le
    (nat.lt_succ_of_le (le_of_face g hg)) (le_of_eq h.symm)))

lemma comp_σ_comp_δ {n m} (f: [n] ⟶ [m + 1]) (i : fin (m + 1))
(hi : ∀ j, f.to_preorder_hom j ≠ i.cast_succ) :
  f ≫ σ i ≫ δ i.cast_succ = f :=
begin
  ext1, ext1 j,
  simp [δ, σ, fin.succ_above, fin.pred_above],
  split_ifs with hij hji hji,
  { rw [←fin.succ_lt_succ_iff, fin.succ_pred, ←fin.le_cast_succ_iff, ←not_lt] at hji,
    exact absurd hij hji, },
  { rwa fin.succ_pred, },
  { rwa fin.cast_succ_cast_lt, },
  { push_neg at hij,
    rw [←fin.cast_succ_lt_cast_succ_iff, not_lt, fin.cast_succ_cast_lt] at hji,
    exact absurd (antisymm hij hji) (hi j),}
end

lemma comp_σ_comp_δ_succ {n m} (f: [n] ⟶ [m + 1]) (i : fin (m + 1))
(hi : ∀ j, f.to_preorder_hom j ≠ i.succ) :
  f ≫ σ i ≫ δ i.succ = f :=
begin
  ext1, ext1 j,
  simp [δ, σ, fin.succ_above, fin.pred_above],
  split_ifs with hij hji hji,
  { rw [←not_le, fin.le_cast_succ_iff, not_lt] at hij hji,
    rw fin.succ_pred at hji,
    exact absurd (antisymm hji hij) (hi j), },
  { rwa fin.succ_pred, },
  { rwa fin.cast_succ_cast_lt, },
  { push_neg at hij,
    rw [fin.cast_succ_cast_lt,←fin.le_cast_succ_iff] at hji,
    exact absurd hij hji, }
end

def inj {n m} (f : [n] ⟶ [m]) := function.injective f.to_preorder_hom

lemma comp_σ_injective {n m} (f: [n] ⟶ [m + 1]) (i : fin (m + 1))
(hi : ∀ j, f.to_preorder_hom j ≠ i.cast_succ) (hf : inj f):
  inj (f ≫ σ i) :=
begin
  intros j k hjk,
  apply hf,
  simp [σ, fin.pred_above] at hjk,
  split_ifs at hjk with hij hik hik,
  { exact fin.pred_inj.mp hjk, },
  { refine absurd (le_antisymm (not_lt.mp hik) _) (hi k),
    rw [←fin.cast_succ_inj, fin.cast_succ_cast_lt] at hjk,
    rwa [←hjk, fin.le_cast_succ_iff, fin.succ_pred], },
  { refine absurd (le_antisymm (not_lt.mp hij) _) (hi j),
    rw [←fin.cast_succ_inj, fin.cast_succ_cast_lt] at hjk,
    rwa [hjk, fin.le_cast_succ_iff, fin.succ_pred], },
  { ext, injections_and_clear, simp at h_1, exact h_1, },
end

lemma comp_σ_injective_succ {n m} (f: [n] ⟶ [m + 1]) (i : fin (m + 1))
(hi : ∀ j, f.to_preorder_hom j ≠ i.succ) (hf : inj f):
  inj (f ≫ σ i) :=
begin
  intros j k hjk,
  apply hf,
  simp [σ, fin.pred_above] at hjk,
  split_ifs at hjk with hij hik hik,
  { exact fin.pred_inj.mp hjk, },
  { refine absurd (le_antisymm _ (by rwa [←not_lt, ←fin.le_cast_succ_iff, not_le])) (hi j),
    rw [←fin.succ_inj, fin.succ_pred] at hjk,
    rw [hjk, ←not_lt, ←fin.le_cast_succ_iff, fin.cast_succ_cast_lt],
    rwa [not_le, ←fin.le_cast_succ_iff, ←not_lt],},
  { refine absurd (le_antisymm _ (by rwa [←not_lt, ←fin.le_cast_succ_iff, not_le])) (hi k),
    rw [←fin.succ_inj, fin.succ_pred] at hjk,
    rw [←hjk, ←not_lt, ←fin.le_cast_succ_iff, fin.cast_succ_cast_lt],
    rwa [not_le, ←fin.le_cast_succ_iff, ←not_lt], },
  { ext, injections_and_clear, simp at h_1, exact h_1, },
end

def fin.find_x {n : ℕ} (p : fin n → Prop) [decidable_pred p] (Hp : ∃ (i : fin n), p i) :
  {i // p i ∧ ∀ j, j < i → ¬p j} :=
begin
  let q : ℕ → Prop := λ i, ∃ (hi : i < n), p ⟨i, hi⟩,
  have Hq : ∃ (i : ℕ), q i,
  { cases Hp with i Hpi, cases i, exact ⟨i_val, i_property, Hpi⟩,},
  let i := nat.find Hq,
  have hi : i < n, cases (nat.find_spec Hq) with hi, exact hi,
  refine ⟨⟨i,hi⟩,_⟩,
  cases (nat.find_spec Hq) with hi hpi,
  split, exact hpi,
  intros j hj hpj,
  cases j,
  exact nat.find_min Hq hj ⟨j_property, hpj⟩,
end

-- /-- TODO: Improve using fin.find -/
-- lemma face_of_injective {n m} (f : [n] ⟶ [m]) (hf : inj f) : nonempty (face f) :=
-- begin
--   induction m with m hm,
--   { have Hf : function.surjective f.to_preorder_hom,
--     { refine λ i, ⟨0,_⟩,
--       rwa[fin.eq_zero (f.to_preorder_hom 0), fin.eq_zero i]},
--     split, exact @face_of_iso _ _ f (iso_of_bijective f ⟨hf, Hf⟩), },
--   by_cases Hf : function.surjective f.to_preorder_hom,
--   { split, exact @face_of_iso _ _ f (iso_of_bijective f ⟨hf, Hf⟩), },
--   { push_neg at Hf,
--     cases Hf with i hi,
--     by_cases Hi: i = 0,
--     { cases Hi,
--       cases hm (f ≫ σ 0) (comp_σ_injective f 0 hi hf) with hfσ,
--       rw [←comp_σ_comp_δ f 0 hi, fin.cast_succ_zero],
--       exact ⟨face.comp (f ≫ σ 0) 0 hfσ⟩ },
--     { let j := i.pred Hi,
--       rw ←fin.succ_pred i Hi at hi,
--       cases hm (f ≫ σ j) (comp_σ_injective_succ f j hi hf) with hfσ,
--       rw [←comp_σ_comp_δ_succ f j hi],
--       exact ⟨face.comp (f ≫ σ j) j.succ hfσ⟩ }},
-- end

lemma face_of_injective {n m} (f : [n] ⟶ [m]) (hf : inj f) : face f :=
begin
  induction m with m hm,
  { have Hf : function.surjective f.to_preorder_hom,
    { refine λ i, ⟨0,_⟩,
      rwa[(f.to_preorder_hom 0).eq_zero , i.eq_zero]},
      exact @face_of_iso _ _ f (iso_of_bijective f ⟨hf, Hf⟩), },
  by_cases Hf : function.surjective f.to_preorder_hom,
  { exact @face_of_iso _ _ f (iso_of_bijective f ⟨hf, Hf⟩), },
  { push_neg at Hf,
    let p := λ i, ∀ j, f.to_preorder_hom j ≠ i,
    let i := (fin.find_x p Hf).1,
    have hi, from (fin.find_x p Hf).2,
    cases hi with hi hi_min,
    clear hi_min,
    change ∀ j, f.to_preorder_hom j ≠ i at hi,
    by_cases Hi: i = 0,
    { have Hi : i.val < [m.succ].len, rw Hi, simp,
      let j := i.cast_lt Hi,
      rw ←fin.cast_succ_cast_lt i Hi at hi,
      let hfσ := hm (f ≫ σ j) (comp_σ_injective f j hi hf),
      rw [←comp_σ_comp_δ f j hi],
      exact face.comp (f ≫ σ j) j.cast_succ hfσ, },
    { let j := i.pred Hi,
      rw ←fin.succ_pred i Hi at hi,
      let hfσ := hm (f ≫ σ j) (comp_σ_injective_succ f j hi hf),
      rw [←comp_σ_comp_δ_succ f j hi],
      exact face.comp (f ≫ σ j) j.succ hfσ }},
end

/-- If f(i) = f(i+1) then σ i ≫ δ i+1 ≫ f = f -/
lemma σ_comp_δ_comp {n m} (f: [n + 1] ⟶ [m]) (i : fin (n + 1))
(H : f.to_preorder_hom i.cast_succ = f.to_preorder_hom i.succ) :
  σ i ≫ δ i.succ ≫ f = f :=
begin
  ext1, ext1 j,
  simp [δ, σ, fin.succ_above, fin.pred_above],
  split_ifs,
  { rw [←not_le, fin.le_cast_succ_iff, not_lt] at h h_1,
    rw fin.succ_pred at h_1,
    cases le_antisymm h_1 h,
    rwa fin.pred_succ, },
  { rw j.succ_pred,},
  { rw fin.cast_succ_cast_lt, },
  { rw [←fin.le_cast_succ_iff, fin.cast_succ_cast_lt, not_le] at h_1,
    exact absurd h_1 h,}
end

-- /-- Every map has a decompostion into a degeneracy and a face map. -/
-- theorem decomp_degeneracy_face : Π {n m} (f : [n] ⟶ [m]),
--   ∃ {k} (s : [n] ⟶ [k]) [degeneracy s] (d : [k] ⟶ [m]) [face d], f = s ≫ d
-- | nat.zero     := λ m f,
-- begin
--   have hf : inj f, intros i j hij, rwa [eq_zero i, eq_zero j],
--   cases face_of_injective f hf with Hf,
--   exact ⟨0, 𝟙 [0], degeneracy.id, f, Hf, (category.id_comp f).symm⟩,
-- end
-- | (nat.succ n) := have n < nat.succ n, from lt_add_one n, λ m f,
-- begin
--   by_cases hf : function.injective f.to_preorder_hom,
--   { cases face_of_injective f hf with Hf,
--     exact ⟨n.succ, 𝟙 [n.succ], degeneracy.id, f, Hf, (category.id_comp f).symm⟩},
--   { push_neg at hf,
--     rcases hf with ⟨j₁, j₂, hfj, hj⟩,
--     wlog j₁lj₂ : j₁ < j₂ := ne.lt_or_lt hj using j₁ j₂,
--     let i := j₁.cast_pred,
--     have hi : f.to_preorder_hom i.cast_succ = f.to_preorder_hom i.succ,
--     { apply le_antisymm,
--       exact f.to_preorder_hom.monotone (le_of_lt (fin.cast_succ_lt_succ i)),
--       rw fin.cast_succ_cast_pred (lt_of_lt_of_le j₁lj₂ (fin.le_last j₂)),
--       rw hfj,
--       apply f.to_preorder_hom.monotone,
--       rw [←not_lt, ←fin.le_cast_succ_iff, not_le],
--       rwa fin.cast_succ_cast_pred (lt_of_lt_of_le j₁lj₂ (fin.le_last j₂)),},
--     clear j₁lj₂ hfj hj j₂,
--     let g := δ i.succ ≫ f,
--     exact have n < nat.succ n, from lt_add_one n, by {
--     rcases decomp_degeneracy_face (δ i.succ ≫ f) with ⟨k, s, hs, d, hd, hsd⟩,
--     refine ⟨k, σ i ≫ s, degeneracy.comp s i hs, d, hd, _⟩,
--     rw [category.assoc, ←hsd],
--     exact (σ_comp_δ_comp f i hi).symm, }}
-- end

/-- Every map has a decompostion into a degeneracy and a face map. -/
theorem decomp_degeneracy_face {n m} (f : [n] ⟶ [m]) :
  ∃ {k} (s : [n] ⟶ [k]) [degeneracy s] (d : [k] ⟶ [m]) [face d], f = s ≫ d :=
begin
  induction n with n ih_n,
  { have hf : inj f, intros i j hij, rwa [i.eq_zero, j.eq_zero],
    exact ⟨0, 𝟙 [0], degeneracy.id, f, face_of_injective f hf, (category.id_comp f).symm⟩,},
  by_cases hf : function.injective f.to_preorder_hom,
  { exact ⟨n.succ, 𝟙 [n.succ], degeneracy.id, f, face_of_injective f hf, (category.id_comp f).symm⟩},
  { push_neg at hf,
    rcases hf with ⟨j₁, j₂, hfj, hj⟩,
    wlog j₁lj₂ : j₁ < j₂ := ne.lt_or_lt hj using j₁ j₂,
    let i := j₁.cast_pred,
    have hi : f.to_preorder_hom i.cast_succ = f.to_preorder_hom i.succ,
    { apply le_antisymm,
      exact f.to_preorder_hom.monotone (le_of_lt (fin.cast_succ_lt_succ i)),
      rw fin.cast_succ_cast_pred (lt_of_lt_of_le j₁lj₂ (fin.le_last j₂)),
      rw hfj,
      apply f.to_preorder_hom.monotone,
      rw [←not_lt, ←fin.le_cast_succ_iff, not_le],
      rwa fin.cast_succ_cast_pred (lt_of_lt_of_le j₁lj₂ (fin.le_last j₂)),},
    clear j₁lj₂ hfj hj j₂,
    let g := δ i.succ ≫ f,
    rcases ih_n g with ⟨k, s, hs, d, hd, hsd⟩,
    refine ⟨k, σ i ≫ s, degeneracy.comp s i hs, d, hd, _⟩,
    rw [category.assoc, ←hsd],
    exact (σ_comp_δ_comp f i hi).symm, }
end

theorem eq_of_same_sections : Π {n m} (s₁ s₂ : [n] ⟶ [m]) [degeneracy s₁] [degeneracy s₂],
(∀ (f : [m] ⟶ [n]), f ≫ s₁ = 𝟙 [m] ↔ f ≫ s₂ = 𝟙 [m]) → s₁ = s₂
| n m s₁ s₂ degeneracy.id               degeneracy.id               := λ hf, rfl
| n m s₁ s₂ (degeneracy.comp g₁ i₁ hg₁) degeneracy.id               :=
  by { intro hf, simpa using (hf (hom.mk preorder_hom.id)),}
| n m s₁ s₂ degeneracy.id               (degeneracy.comp g₂ i₂ hg₂) :=
  by {intro hf, symmetry, simpa using (hf (hom.mk preorder_hom.id)), }
| n m s₁ s₂ (degeneracy.comp g₁ i₁ hg₁) (degeneracy.comp g₂ i₂ hg₂) :=
begin
  intro hf,
  -- by_cases hi : i₁ = i₂,
  ext1, ext1 i,
  simp [σ, fin.pred_above],
  split_ifs,
  { apply congr_fun, apply congr_arg, apply congr_arg,
    sorry },
  {
    sorry },
  {
    sorry },
  { apply congr_fun, apply congr_arg, apply congr_arg,
    sorry }
end

end simplex_category
