import traversals.basic
import category_theory.currying

open category_theory
open category_theory.limits
open simplex_category
open sSet
open_locale simplicial

namespace traversal

namespace geom_real_rec

variables {n : ℕ}

def s : edge n → fin (n+2)
| ⟨k, ∔⟩ := k.succ
| ⟨k, ∸⟩ := k.cast_succ

def t : edge n → fin (n+2)
| ⟨k, ∔⟩ := k.cast_succ
| ⟨k, ∸⟩ := k.succ

notation e`ᵗ` := t e
notation e`ˢ` := s e

def sSet_colimit {sh : Type*} [small_category sh] (diag : sh ⥤ sSet) :
  colimit_cocone (diag) :=
{ cocone := combine_cocones (diag) (λ n,
  { cocone := types.colimit_cocone _,
    is_colimit := types.colimit_cocone_is_colimit _ }),
  is_colimit := combined_is_colimit _ _, }

def sSet_pushout {X Y Z : sSet} (f : X ⟶ Y) (g : X ⟶ Z) := sSet_colimit (span f g)

def bundle : Π (θ : traversal n), Σ (g : sSet), Δ[n] ⟶ g
| ⟦⟧       := ⟨Δ[n], 𝟙 _⟩
| (e :: θ) :=
  let colim := sSet_pushout (to_sSet_hom (δ (eᵗ))) (bundle θ).2 in
  ⟨colim.cocone.X, to_sSet_hom (δ (s e)) ≫ pushout_cocone.inl colim.cocone⟩

end geom_real_rec

def geom_real_rec {n} (θ : traversal n) : sSet := (geom_real_rec.bundle θ).1

namespace geom_real_rec
variables {n : ℕ}

def geom_real_incl (θ : traversal n) : Δ[n] ⟶ geom_real_rec θ := (geom_real_rec.bundle θ).2

def bundle_colim (e : edge n) (θ : traversal n) :=
  sSet_pushout (to_sSet_hom (δ (t e))) (bundle θ).2

@[simp]
lemma geom_real_rec_nil : geom_real_rec (⟦⟧ : traversal n) = Δ[n] := rfl

@[simp]
lemma geom_real_incl_nil : geom_real_incl (⟦⟧ : traversal n) = 𝟙 Δ[n] := rfl

lemma geom_real_rec_cons (e : edge n) (θ : traversal n) :
  geom_real_rec (e :: θ) = (bundle_colim e θ).cocone.X := rfl

lemma geom_real_incl_cons (e : edge n) (θ : traversal n) :
  geom_real_incl (e :: θ) = to_sSet_hom (δ (s e))
    ≫ pushout_cocone.inl (bundle_colim e θ).cocone := rfl

def j_rec_bundle : Π (θ : traversal n),
  {j : geom_real_rec θ ⟶ Δ[n] // geom_real_incl θ ≫ j = 𝟙 Δ[n]}
| ⟦⟧       := ⟨𝟙 Δ[n], rfl⟩
| (e :: θ) :=
begin
  let j_θ := j_rec_bundle θ,
  refine ⟨(bundle_colim e θ).is_colimit.desc (pushout_cocone.mk (to_sSet_hom (σ e.1)) j_θ.1 _), _⟩,
  change _ = geom_real_incl θ ≫ j_θ.val, rw j_θ.2,
  swap,
  rw [geom_real_incl_cons, category.assoc],
  rw [(bundle_colim e θ).is_colimit.fac _ walking_span.left, pushout_cocone.mk_ι_app_left],
  all_goals
  { dsimp [to_sSet_hom],
    rw [←standard_simplex.map_comp, ←standard_simplex.map_id],
    apply congr_arg,
    cases e with i b, cases b;
    try { exact δ_comp_σ_self };
    try { exact δ_comp_σ_succ }},
end

def j_rec (θ : traversal n) : geom_real_rec θ ⟶ Δ[n] := (j_rec_bundle θ).1

def j_prop (θ : traversal n) : geom_real_incl θ ≫ j_rec θ = 𝟙 Δ[n] := (j_rec_bundle θ).2

@[simp] lemma apply_δ_self {n} (i : fin (n + 2)) (b : ±) :
  apply_map_to_edge (δ i) (i, b) = ⟦⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  apply apply_map_to_edge_sorted,
  exact list.sorted_nil,
  intro e, cases e, simp,
  intro h, exfalso,
  simp [δ, fin.succ_above] at h,
  split_ifs at h,
  finish,
  rw [not_lt, fin.le_cast_succ_iff] at h_1, finish,
end

@[simp] lemma apply_δ_succ_cast_succ {n} (i : fin (n + 1)) (b : ±) :
  apply_map_to_edge (δ i.succ) (i.cast_succ, b) = ⟦(i, b)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  apply apply_map_to_edge_sorted,
  exact list.sorted_singleton (i, b),
  intro e, cases e, simp,
  intro hb, cases hb,
  split,
  { intro he,
    have H : (δ i.succ ≫ σ i).to_preorder_hom e_fst = (σ i).to_preorder_hom i.cast_succ,
    { rw ←he, simp, },
    rw δ_comp_σ_succ at H,
    simpa [σ, fin.pred_above] using H, },
  { intro he, cases he,
    simp [δ, fin.succ_above, fin.cast_succ_lt_succ], }
end

@[simp] lemma apply_δ_cast_succ_succ {n} (i : fin (n + 1)) (b : ±) :
  apply_map_to_edge (δ i.cast_succ) (i.succ, b) = ⟦(i, b)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  apply apply_map_to_edge_sorted,
  exact list.sorted_singleton (i, b),
  intro e, cases e, simp,
  intro hb, cases hb,
  split,
  { intro he,
    have H : (δ i.cast_succ ≫ σ i).to_preorder_hom e_fst = (σ i).to_preorder_hom i.succ,
    { rw ←he, simp, },
    rw δ_comp_σ_self at H,
    simp [σ, fin.pred_above] at H,
    split_ifs at H, from H,
    exact absurd (fin.cast_succ_lt_succ i) h, },
  { intro he, cases he,
    simp [δ, fin.succ_above, fin.cast_succ_lt_succ], }
end

def k_rec_bundle : Π (θ θ' : traversal n),
  {k : geom_real_rec θ ⟶ 𝕋₁ // geom_real_incl θ ≫ k = simplex_as_hom (θ', θ)}
| ⟦⟧       θ' := ⟨simplex_as_hom (θ',⟦⟧), rfl⟩
| (e :: θ) θ' :=
begin
  let k_θ := k_rec_bundle θ (θ' ++ ⟦e⟧),
  refine ⟨(bundle_colim e θ).is_colimit.desc (pushout_cocone.mk _ k_θ.1 _), _⟩,
  { apply simplex_as_hom,
    --Special position
    exact (apply_map (σ e.1) θ' ++ ⟦(s e, e.2)⟧, (t e, e.2) :: apply_map (σ e.1) θ)},
  change _ = geom_real_incl θ ≫ k_θ.val, rw k_θ.2,
  swap,
  rw [geom_real_incl_cons, category.assoc],
  rw [(bundle_colim e θ).is_colimit.fac _ walking_span.left, pushout_cocone.mk_ι_app_left],
  all_goals
  { rw [hom_comp_simplex_as_hom],
    rw simplex_as_hom_eq_iff,
    cases e with i b, cases b; simp;
    rw [𝕋₀_map_apply, 𝕋₀_map_apply, has_hom.hom.unop_op];
    simp[s, t, apply_map];
    rw [←apply_comp, ←apply_comp];
    try { rw δ_comp_σ_self }; try { rw δ_comp_σ_succ };
    rw [apply_id, apply_id];
    simp },
end

def k_rec' (θ θ' : traversal n) := (k_rec_bundle θ θ').1

def k_prop' (θ θ' : traversal n) :
  geom_real_incl θ ≫ k_rec' θ θ' = simplex_as_hom (θ', θ) := (k_rec_bundle θ θ').2

def k_rec (θ : traversal n) : geom_real_rec θ ⟶ 𝕋₁ := (k_rec_bundle θ ⟦⟧).1

def k_prop (θ : traversal n) :
  geom_real_incl θ ≫ k_rec θ = simplex_as_hom (⟦⟧, θ) := (k_rec_bundle θ ⟦⟧).2

@[simp] lemma apply_σ_to_plus (i : fin (n + 1)) :
  apply_map_to_edge (σ i) (i, ∔) = ⟦(i.succ, ∔), (i.cast_succ, ∔)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_to_edge_sorted,},
  { simp [sorted], intros a b ha hb, rw ha, rw hb,
    exact fin.cast_succ_lt_succ i, },
  { intro e, cases e with l b,
    rw edge_in_apply_map_to_edge_iff,
    simp, rw ←or_and_distrib_right, simp, intro hb, clear hb b,
    simp [σ, fin.pred_above],
    split,
    { intro H, split_ifs at H,
      rw ←fin.succ_inj at H, simp at H,
      left, exact H,
      rw ←fin.cast_succ_inj at H, simp at H,
      right, exact H, },
    { intro H, cases H; rw H; simp[fin.cast_succ_lt_succ], }}
end

@[simp] lemma apply_σ_to_min (i : fin (n + 1)) :
  apply_map_to_edge (σ i) (i, ∸) = ⟦(i.cast_succ, ∸), (i.succ, ∸)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_to_edge_sorted, },
  { simp[sorted],
    intros a b ha hb, rw [ha, hb],
    exact fin.cast_succ_lt_succ i, },
  { intro e, cases e with l b,
    rw edge_in_apply_map_to_edge_iff,
    simp, rw ←or_and_distrib_right, simp, intro hb, clear hb b,
    simp [σ, fin.pred_above],
    split,
    { intro H, split_ifs at H,
      rw ←fin.succ_inj at H, simp at H,
      right, exact H,
      rw ←fin.cast_succ_inj at H, simp at H,
      left, exact H, },
    { intro H, cases H; rw H; simp[fin.cast_succ_lt_succ], }}
end

lemma apply_σ_to_self (e : edge n) :
  apply_map_to_edge (σ e.1) e = ⟦(s e, e.2), (t e, e.2)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_to_edge_sorted, },
  { simp[sorted],
    intros a b ha hb, rw [ha, hb],
    cases e with i, cases e_snd;
    exact fin.cast_succ_lt_succ i, },
  { sorry,
    -- intro e', cases e with l b,
    -- rw edge_in_apply_map_to_edge_iff,
    -- simp,-- rw ←or_and_distrib_right, simp, intro hb, clear hb b,
    -- simp [σ, fin.pred_above],
    -- split,
    -- { intro H, split_ifs at H,
    --   rw ←fin.succ_inj at H, simp at H,
    --   right, ext, exact H.1, exact H.2,
    --   rw ←fin.cast_succ_inj at H, simp at H,
    --   left, exact H, },
    -- { intro H, cases H; rw H; simp[fin.cast_succ_lt_succ], }
    }
end

lemma j_comp_θ_eq_k_comp_cod : Π (θ θ' : traversal n),
  j_rec θ ≫ (θ' ++ θ).as_hom = (k_rec_bundle θ θ').1 ≫ cod
| ⟦⟧       θ' :=
  begin
    change simplex_as_hom _ = simplex_as_hom _ ≫ cod,
    rw [simplex_as_hom_comp_hom], refl,
  end
| (e :: θ) θ' :=
begin
  apply pushout_cocone.is_colimit.hom_ext (bundle_colim e θ).is_colimit,
  { change to_sSet_hom (σ e.fst) ≫ simplex_as_hom _ = simplex_as_hom _ ≫ cod,
    rw [simplex_as_hom_comp_hom, hom_comp_simplex_as_hom],
    rw simplex_as_hom_eq_iff,
    dsimp [𝕋₀, apply_map, cod], cases e with i b, cases b; simp,
    all_goals { simp [apply_map], change _ = _ ++ _, rw list.append_assoc, refl,}},
  { change j_rec θ ≫ (θ' ++ (⟦e⟧ ++ θ)).as_hom = (k_rec_bundle θ (θ' ++ ⟦e⟧)).1 ≫ cod,
    rw ←list.append_assoc,
    apply j_comp_θ_eq_k_comp_cod }
end

def pullback_cone_rec' (θ θ' : traversal n) : pullback_cone ((θ' ++ θ).as_hom) cod :=
  pullback_cone.mk (j_rec θ) (k_rec_bundle θ θ').1 (j_comp_θ_eq_k_comp_cod θ θ')

def pullback_cone_rec (θ : traversal n) : pullback_cone (θ.as_hom) cod :=
  pullback_cone.mk (j_rec θ) (k_rec θ) (j_comp_θ_eq_k_comp_cod θ ⟦⟧)

def append_eq_append_split {n} {a b c d : traversal n} :
  a ++ b = c ++ d → (Σ e, {a' // c = a ++ e :: a' ∧ b = e :: a' ++ d}) ⊕ {c' // a = c ++ c' ∧ d = c' ++ b} :=
begin
  induction c generalizing a,
  case nil { rw list.nil_append, rintro rfl, right, exact ⟨a, rfl, rfl⟩ },
  case cons : c cs ih {
    intro h, cases a,
    { left, use c, use cs, simpa using h },
    { simp at h, cases h, cases h_left, simp,
      exact ih h_right }}
end

def data_of_split {m} {α : m ⟶ [n]} {e} {e₁ e₂} {θ₁ a'} (H : apply_map_to_edge α e = e₁ :: θ₁ ++ e₂ :: a') :
  { k : fin m.len //
    α.to_preorder_hom k.cast_succ = e.1 ∧
    α.to_preorder_hom k.succ = e.1 ∧
    (α.to_preorder_hom e₁.1, e₁.2) = e ∧
    (α.to_preorder_hom e₂.1, e₂.2) = e ∧
    e₁ < e₂ } :=
begin
  have he₁ : (α.to_preorder_hom e₁.1, e₁.2) = e,
  { rw [←edge_in_apply_map_to_edge_iff, H], simp, },
  have he₂ : (α.to_preorder_hom e₂.1, e₂.2) = e,
  { rw [←edge_in_apply_map_to_edge_iff, H], simp, },
  have he₁₂ : e₁ < e₂,
  { have h := apply_map_to_edge_sorted α e,
    rw H at h, dsimp[sorted] at h,
    rw list.sorted_cons at h,
    refine h.1 e₂ (list.mem_append_right _ (list.mem_cons_self e₂ a')) },
  cases e with i b, cases b,
  { refine ⟨e₂.1.cast_lt _, _, _, he₁, he₂, he₁₂⟩;
    cases e₁ with i₁; cases e₂ with i₂; simp at he₁ he₂;
    cases he₁.2; cases he₂.2; simp at he₁ he₂,
    exact lt_of_lt_of_le he₁₂ (nat.le_of_lt_succ i₁.prop),
    simpa using he₂, simp,
    apply le_antisymm,
    { cases he₁, apply α.to_preorder_hom.monotone,
      rw [←not_lt, ←fin.le_cast_succ_iff, not_le],
      exact he₁₂, },
    { cases he₂, apply α.to_preorder_hom.monotone,
      exact le_trans (by simp) (le_of_lt (fin.cast_succ_lt_succ _)) } },
  { refine ⟨e₂.1.pred _, _, _, he₁, he₂, he₁₂⟩;
    cases e₁ with i₁; cases e₂ with i₂; simp at he₁ he₂;
    cases he₁.2; cases he₂.2; simp at he₁ he₂,
    exact ne_of_gt (lt_of_le_of_lt (fin.zero_le i₁) he₁₂),
    simp, apply le_antisymm,
    { cases he₂, apply α.to_preorder_hom.monotone,
      refine le_trans (le_of_lt (fin.cast_succ_lt_succ _)) (by simp) },
    { cases he₁, apply α.to_preorder_hom.monotone,
      rw [fin.le_cast_succ_iff, fin.succ_pred],
      exact he₁₂ },
    simpa using he₂ }
end

lemma of_split {m} {α : m ⟶ [n]} {e} {e₁ e₂} {θ₁ a'} (H : apply_map_to_edge α e = e₁ :: θ₁ ++ e₂ :: a') :
  (α.to_preorder_hom e₁.1, e₁.2) = e ∧
  (α.to_preorder_hom e₂.1, e₂.2) = e ∧
  e₁ < e₂ :=
begin
  split,
  rw [←edge_in_apply_map_to_edge_iff, H], simp,
  split,
  rw [←edge_in_apply_map_to_edge_iff, H], simp,
  have h := apply_map_to_edge_sorted α e,
  rw H at h, dsimp[sorted] at h,
  rw list.sorted_cons at h,
  refine h.1 e₂ (list.mem_append_right _ (list.mem_cons_self e₂ a'))
end

def k_of_split {m} {α : m ⟶ [n]} {e} {e₁ e₂} {θ₁ a'} (H : apply_map_to_edge α e = e₁ :: θ₁ ++ e₂ :: a') :
  fin m.len  :=
begin
  cases e with i b, cases b,
  { refine e₂.1.cast_lt _,
    rcases of_split H with ⟨he₁, he₂, he₁₂⟩,
    cases e₁ with i₁; cases e₂ with i₂; simp at he₁ he₂;
    cases he₁.2; cases he₂.2; simp at he₁ he₂,
    exact lt_of_lt_of_le he₁₂ (nat.le_of_lt_succ i₁.prop) },
  { refine e₂.1.pred _,
    rcases of_split H with ⟨he₁, he₂, he₁₂⟩,
    cases e₁ with i₁; cases e₂ with i₂; simp at he₁ he₂;
    cases he₁.2; cases he₂.2; simp at he₁ he₂,
    exact ne_of_gt (lt_of_le_of_lt (fin.zero_le i₁) he₁₂) }
end

lemma α_k_of_split {m} {α : m ⟶ [n]} {e} {e₁ e₂} {θ₁ a'} (H : apply_map_to_edge α e = e₁ :: θ₁ ++ e₂ :: a') :
  α.to_preorder_hom (k_of_split H).cast_succ = e.1 ∧ α.to_preorder_hom (k_of_split H).succ = e.1 :=
begin
  rcases of_split H with ⟨he₁, he₂, he₁₂⟩,
  split; cases e with i b; cases b;
  simp [k_of_split];
  cases e₁ with i₁; cases e₂ with i₂; simp at he₁ he₂;
  cases he₁.2; cases he₂.2; simp at he₁ he₂ ⊢;
  try { exact he₂ };
  apply le_antisymm,
  { cases he₂, apply α.to_preorder_hom.monotone,
    refine le_trans (le_of_lt (fin.cast_succ_lt_succ _)) (by simp) },
  { cases he₁, apply α.to_preorder_hom.monotone,
    rw [fin.le_cast_succ_iff, fin.succ_pred],
    exact he₁₂ },
  { cases he₁, apply α.to_preorder_hom.monotone,
    rw [←not_lt, ←fin.le_cast_succ_iff, not_le],
    exact he₁₂, },
  { cases he₂, apply α.to_preorder_hom.monotone,
    refine le_trans (by simp) (le_of_lt (fin.cast_succ_lt_succ _)) }
end

def β {m} (α : m ⟶ [n]) (k : fin m.len) :
-- (hk₁ : α.to_preorder_hom k.cast_succ = i) (hk₂ : α.to_preorder_hom k.succ = i) :
  m ⟶ [n+1]  := hom.mk
{ to_fun    := λ j, if j ≤ k.cast_succ then (α.to_preorder_hom j).cast_succ else (α.to_preorder_hom j).succ,
  monotone' :=
  begin
    intros j₁ j₂ hj, simp, split_ifs, simp,
    exact α.to_preorder_hom.monotone hj,
    calc
    (α.to_preorder_hom j₁).cast_succ ≤ (α.to_preorder_hom j₁).succ : le_of_lt (fin.cast_succ_lt_succ _)
                                  ... ≤ (α.to_preorder_hom j₂).succ : by simp [α.to_preorder_hom.monotone hj],
    exact absurd (le_trans hj h_1) h,
    simp [α.to_preorder_hom.monotone hj],
  end }

lemma β_comp_σ {m} (α : m ⟶ [n]) {i} {k : fin m.len} (hk₁ : α.to_preorder_hom k.cast_succ = i) (hk₂ : α.to_preorder_hom k.succ = i) :
  β α k ≫ σ i = α :=
begin
  ext, simp[σ, fin.pred_above, β], split_ifs; simp [h]; split_ifs;
  try { refl },
  exact absurd hk₁ (ne_of_gt (lt_of_lt_of_le h_1 (α.to_preorder_hom.monotone h))),
  rw [←fin.le_cast_succ_iff, not_le, fin.cast_succ_lt_cast_succ_iff] at h_1,
  exact absurd hk₁ (ne_of_lt (lt_of_le_of_lt (α.to_preorder_hom.monotone (le_of_not_ge h)) h_1)),
end

lemma βk_neq_βksucc {m} (α : m ⟶ [n]) {i} {k : fin m.len} (hk₁ : α.to_preorder_hom k.cast_succ = i) (hk₂ : α.to_preorder_hom k.succ = i) :
  (β α k).to_preorder_hom k.cast_succ ≠ (β α k).to_preorder_hom k.succ :=
begin
  dsimp[β], rw hom.to_preorder_hom_mk,
  intro h,
  rw [preorder_hom.coe_fun_mk, preorder_hom.coe_fun_mk] at h,
  simp [le_refl, not_le.mpr (fin.cast_succ_lt_succ k)] at h,
  rw [hk₁, hk₂] at h,
  refine absurd (fin.cast_succ_lt_succ i) _,
  rw [h, not_lt],
end


def geom_real_rec_lift' : Π (θ θ' : traversal n) {m} (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (geom_real_rec θ).obj (opposite.op m)
| ⟦⟧       θ' m α θ₁         θ₂ hθ := α
| (e :: θ) θ' m α ⟦⟧         θ₂ hθ := (geom_real_incl (e :: θ)).app (opposite.op m) α
| (e :: θ) θ' m α (e₁ :: θ₁) θ₂ hθ :=
  begin
    cases append_eq_append_split hθ with a' c',
    { rcases a' with ⟨e₂, a', ha'⟩,
      let p : pushout_cocone _ _ := (bundle_colim e θ).cocone,
      apply p.inl.app (opposite.op m),
      exact β α (k_of_split ha'.1),
      -- have he₂ : (α.to_preorder_hom e₂.1, e₂.2) = e,
      -- { rw [←edge_in_apply_map_to_edge_iff, ha'.1], simp, },
      -- have he₁ : (α.to_preorder_hom e₁.1, e₁.2) = e,
      -- { rw [←edge_in_apply_map_to_edge_iff, ha'.1], simp, },
      -- have he₁₂ : e₁ < e₂,
      -- { have H := apply_map_to_edge_sorted α e,
      --   rw ha'.1 at H, dsimp[sorted] at H,
      --   rw list.sorted_cons at H,
      --   refine H.1 e₂ (list.mem_append_right _ (list.mem_cons_self e₂ a')) },
      -- cases e with i b, cases b,
      -- { refine β α (e₂.1.cast_lt _),
      --   cases e₁, cases e₂, simp at *,
      --   cases he₁.2, cases he₂.2,
      --   exact lt_of_lt_of_le he₁₂ (nat.le_of_lt_succ e₁_fst.prop) },
      -- { refine β α (e₂.1.pred _),
      --   cases e₁, cases e₂, simp at *,
      --   cases he₁.2, cases he₂.2, simp at *,
      --   exact ne_of_gt (lt_of_le_of_lt (fin.zero_le e₁_fst) he₁₂) }
    },
    { cases c' with c' hc',
      let p : pushout_cocone _ _ := (bundle_colim e θ).cocone,
      exact p.inr.app (opposite.op m) (geom_real_rec_lift' θ (θ' ++ ⟦e⟧) α c' θ₂ hc'.2.symm) },
  end

lemma geom_real_rec_fac_j' : Π (θ θ' : traversal n) {m} (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (j_rec θ).app (opposite.op m) (geom_real_rec_lift' θ θ' α θ₁ θ₂ hθ) = α
| ⟦⟧       θ' m α θ₁ θ₂ hθ := rfl
| (e :: θ) θ' m α ⟦⟧ θ₂ hθ :=
  begin
    change (geom_real_incl (e :: θ) ≫ j_rec (e :: θ)).app (opposite.op m) α = α,
    rw j_prop, refl,
  end
| (e :: θ) θ' m α (e₁ :: θ₁) θ₂ hθ :=
  begin
    simp [geom_real_rec_lift'],
    cases append_eq_append_split hθ with a' c',
    { rcases a' with ⟨e₂, a', ha'⟩,
      cases e with i b, simp,
      let H := α_k_of_split ha'.1,
      change β α _ ≫ σ i = α,
      apply β_comp_σ,
      exact H.1,
      exact H.2, },
      -- have he₂ : (α.to_preorder_hom e₂.1, e₂.2) = e,
      -- { rw [←edge_in_apply_map_to_edge_iff, ha'.1], simp, },
      -- have he₁ : (α.to_preorder_hom e₁.1, e₁.2) = e,
      -- { rw [←edge_in_apply_map_to_edge_iff, ha'.1], simp, },
      -- have he₁₂ : e₁ < e₂,
      -- { have H := apply_map_to_edge_sorted α e,
      --   rw ha'.1 at H, dsimp[sorted] at H,
      --   rw list.sorted_cons at H,
      --   refine H.1 e₂ (list.mem_append_right _ (list.mem_cons_self e₂ a')) },
      -- simp [j_rec, j_rec_bundle],
      -- cases e with i b, cases b;
      -- cases e₁; cases e₂; simp at he₁ he₂;
      -- cases he₁.2; cases he₂.2; simp at he₁ he₂;
      -- change β α _ ≫ σ i = α;
      -- apply β_comp_σ;
      -- try { simpa using he₂ };
      -- apply le_antisymm,
      -- { cases he₁, apply α.to_preorder_hom.monotone,
      --   rw [←not_lt, ←fin.le_cast_succ_iff, not_le],
      --   exact he₁₂, },
      -- { cases he₂, apply α.to_preorder_hom.monotone,
      --   refine le_trans (by simp) (le_of_lt (fin.cast_succ_lt_succ _)) },
      -- { cases he₂, apply α.to_preorder_hom.monotone,
      --   refine le_trans (le_of_lt (fin.cast_succ_lt_succ _)) (by simp) },
      -- { cases he₁, apply α.to_preorder_hom.monotone,
      --   rw [fin.le_cast_succ_iff, fin.succ_pred],
      --   exact he₁₂ }},
    { cases c' with c' hc',
      exact geom_real_rec_fac_j' θ (θ' ++ ⟦e⟧) α c' θ₂ _ }
  end

lemma mem_left_iff_of_sorted : Π {θ₁ θ₂ : traversal n} {e} (e') (H : sorted (θ₁ ++ e :: θ₂)),
  e' ∈ θ₁ ↔ e' ∈ θ₁ ++ e :: θ₂ ∧ e' < e
| ⟦⟧ θ₂ e e' H :=
begin
  dsimp [sorted] at H, simp,
  rw list.sorted_cons at H,
  replace H := H.1 e',
  intro h, cases h, cases h,
  exact λ h', edge.lt_asymm e e h' h',
  exact λ h', edge.lt_asymm e e' (H h) h',
end
| (e₁ :: θ₁) θ₂ e e' H :=
begin
  dsimp [sorted] at H,
  rw list.sorted_cons at H,
  rw [list.mem_cons_iff, list.cons_append, list.mem_cons_iff],
  rw mem_left_iff_of_sorted e' H.2,
  rw or_and_distrib_left,
  suffices h : e' = e₁ ∨ e' < e ↔ e' < e, rw h, simp,
  intro h, rw h,
  exact H.1 e (by simp),
end

lemma geom_real_rec_fac_k' : Π (θ θ' : traversal n) {m} (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (k_rec_bundle θ θ').1.app (opposite.op m) (geom_real_rec_lift' θ θ' α θ₁ θ₂ hθ) = ((apply_map α θ') ++ θ₁, θ₂)
| ⟦⟧       θ' m α θ₁ θ₂ hθ :=
  begin
    simp [apply_map] at hθ,
    cases hθ.1, cases hθ.2,
    simp[geom_real_rec_lift'], refl
  end
| (e :: θ) θ' m α ⟦⟧ θ₂ hθ :=
  begin
    simp at hθ, cases hθ,
    simp[k_rec_bundle],
    change (geom_real_incl (e :: θ) ≫ k_rec' (e :: θ) θ').app (opposite.op m) α = _,
    rw k_prop', refl,
  end
| (e :: θ) θ' m α (e₁ :: θ₁) θ₂ hθ :=
  begin
    simp [geom_real_rec_lift'],
    cases append_eq_append_split hθ with a' c',
    { rcases a' with ⟨e₂, a', ha'⟩, simp,
      cases e with i b, --simp,
      let H := α_k_of_split ha'.1,
      change (simplex_as_hom _).app (opposite.op m) (β α _) = _,
      simp [simplex_as_hom],
      change apply_map _ _  = _ ∧ apply_map _ _  = _ ,
      rw [apply_map_append],
      simp [apply_map],
      rw [←apply_comp, ←apply_comp, β_comp_σ α H.1 H.2],
      cases ha'.2,
      change _ ∧ _ = (e₂ :: a') ++ _,
      rw [list.append_left_inj],
      rw [list.append_right_inj],
      have h₁ : sorted (e₁ :: θ₁ ++ e₂ :: a'), rw ←ha'.1, apply apply_map_to_edge_sorted,
      have h₂ := h₁, rw ←append_sorted_iff at h₂,
      split;
      refine eq_of_sorted_of_same_elem _ _ (apply_map_to_edge_sorted _ _) (by simp[h₂.1, h₂.2]) _;
      {
        intro e,
        rw [mem_left_iff_of_sorted e h₁, ←ha'.1],
        suffices H' : _ ↔ e ∈ apply_map (β α _ ≫ σ i) ⟦(i, b)⟧ ∧ e < e₂,
        { rw β_comp_σ α H.1 H.2 at H',
          dsimp [apply_map] at H', rw list.append_nil at H',
          exact H' },
        rw apply_comp, simp only [apply_map, list.append_nil],
        simp,
        simp [σ, fin.pred_above, β],
      }
      -- have he₂ : (α.to_preorder_hom e₂.1, e₂.2) = e,
      -- { rw [←edge_in_apply_map_to_edge_iff, ha'.1], simp, },
      -- have he₁ : (α.to_preorder_hom e₁.1, e₁.2) = e,
      -- { rw [←edge_in_apply_map_to_edge_iff, ha'.1], simp, },
      -- have he₁₂ : e₁ < e₂,
      -- { have H := apply_map_to_edge_sorted α e,
      --   rw ha'.1 at H, dsimp[sorted] at H,
      --   rw list.sorted_cons at H,
      --   refine H.1 e₂ (list.mem_append_right _ (list.mem_cons_self e₂ a')) },
      -- simp [k_rec_bundle];
      -- cases e with i b, cases b;
      -- simp at he₁; simp at he₂;
      -- change (simplex_as_hom _).app (opposite.op m) (β α _) = _,
      -- simp [simplex_as_hom],
      -- -- change _ ⬝ (β α _) = _,
      -- sorry

    },
    { cases c' with c' hc', simp,
      dsimp [k_rec, k_rec_bundle],
      change (k_rec_bundle θ (θ' ++ ⟦e⟧)).1.app (opposite.op m) (geom_real_rec_lift' θ (θ' ++ ⟦e⟧) α c' θ₂ _) = _,
      rw [hc'.1, ←list.append_assoc],
      specialize geom_real_rec_fac_k' θ (θ' ++ ⟦e⟧) α c' θ₂ hc'.2.symm,
      rw [geom_real_rec_fac_k', apply_map_append],
      simp [list.append_assoc, apply_map] }
  end

def geom_real_rec_lift (θ : traversal n) {m} : Π (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (geom_real_rec θ).obj (opposite.op m) := geom_real_rec_lift' θ ⟦⟧


lemma geom_real_rec_fac_j (θ : traversal n) {m} : Π (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (j_rec θ).app (opposite.op m) (geom_real_rec_lift θ α θ₁ θ₂ hθ) = α := geom_real_rec_fac_j' θ ⟦⟧


lemma geom_real_rec_fac_k (θ : traversal n) {m} : Π (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (k_rec θ).app (opposite.op m) (geom_real_rec_lift θ α θ₁ θ₂ hθ) = (θ₁, θ₂) := geom_real_rec_fac_k' θ ⟦⟧

lemma geom_real_rec_unique : Π (θ : traversal n) {m} (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ)
  (x : (geom_real_rec θ).obj (opposite.op m)),
  (j_rec θ).app (opposite.op m) x = α →
  (k_rec θ).app (opposite.op m) x = (θ₁, θ₂) →
  x = geom_real_rec_lift θ α θ₁ θ₂ hθ
| ⟦⟧ m α θ₁ θ₂ hθ x hx₁ hx₂ :=
  begin
    dsimp [geom_real_rec_lift],
    rw ←hx₁, refl,
  end
| (e :: θ) m α ⟦⟧ θ₂ hθ x hx₁ hx₂ :=
  begin
    dsimp [geom_real_rec_lift],
    -- simp at hθ, cases hθ, clear hθ,
    -- rw geom_real_incl_cons,
    -- -- dsimp[geom_real_incl],
    -- rw hx₁.symm at hx₂ ⊢,
    sorry
  end
| (e :: θ) m α (e₁ :: θ₁) θ₂ hθ x hx₁ hx₂ :=
  begin
    sorry
  end

theorem geom_real_is_pullback_θ_cod (θ : traversal n) : is_limit (pullback_cone_rec θ) :=
begin
  apply evaluation_jointly_reflects_limits,
  intro m, exact
  { lift := λ c,
    begin
      let c_fst : c.X ⟶ Δ[n].obj m := c.π.app walking_cospan.left,
      let c_snd : c.X ⟶ 𝕋₁.obj m   := c.π.app walking_cospan.right,
      have hθ : c_fst ≫ (as_hom θ).app m = c_snd ≫ cod.app m,
      { change c_fst ≫ (cospan θ.as_hom cod ⋙ (evaluation simplex_categoryᵒᵖ Type).obj m).map walking_cospan.hom.inl
          = c_snd ≫ (cospan θ.as_hom cod ⋙ (evaluation simplex_categoryᵒᵖ Type).obj m).map walking_cospan.hom.inr,
        rw [←c.π.naturality, ←c.π.naturality], refl },
      exact λ x, geom_real_rec_lift θ (c_fst x) _ _ (congr_fun hθ x).symm,
    end,
    fac' := λ c,
    begin
      intro j, cases j;
      let c_fst : c.X ⟶ Δ[n].obj m := c.π.app walking_cospan.left;
      let c_snd : c.X ⟶ pointed_traversal m.unop.len := c.π.app walking_cospan.right,

      { let p := pullback_cone_rec θ,
        let const_c := (category_theory.functor.const walking_cospan).obj c.X,
        let const_c_inl := const_c.map walking_cospan.hom.inl,
        let const_p := (category_theory.functor.const walking_cospan).obj p.X,
        let const_p_inl := const_p.map walking_cospan.hom.inl,
        let eval_cospan := cospan θ.as_hom cod ⋙ (evaluation simplex_categoryᵒᵖ Type).obj m,
        change _ = const_c_inl ≫ c.π.app none,
        have H : const_c_inl ≫ c.π.app none = _, apply c.π.naturality',
        refine trans _ H.symm, clear H,
        suffices H : ((pullback_cone_rec θ).π.app none).app m
          = ((pullback_cone_rec θ).π.app walking_cospan.left).app m
          ≫ eval_cospan.map walking_cospan.hom.inl,
        { simp, rw H, ext1 x,
          let α : m.unop ⟶ [n] := c_fst x,
          simp, apply congr_arg,
          exact geom_real_rec_fac_j θ α _ _ _ },
        change (const_p_inl ≫ (pullback_cone_rec θ).π.app none).app m = _,
        rw p.π.naturality', refl },
      ext1 x, let α : m.unop ⟶ [n] := c_fst x,
      cases j, simp,
      { exact geom_real_rec_fac_j θ α _ _ _ },
      { change (k_rec θ).app (opposite.op m.unop) (geom_real_rec_lift θ α (c_snd x).1 (c_snd x).2 _) = c_snd x,
        rw [geom_real_rec_fac_k θ α (c_snd x).1 (c_snd x).2 _], simp }
    end,
    uniq' := λ c,
    begin
      intros lift' hlift',
      change c.X ⟶ (geom_real_rec θ).obj (opposite.op m.unop) at lift',
      ext1 x, simp,
      apply geom_real_rec_unique θ,
      specialize hlift' walking_cospan.left, simp at hlift',
      rw ←hlift', refl,
      specialize hlift' walking_cospan.right, simp at hlift',
      rw ←hlift',
      simp, refl,
    end }
end

end geom_real_rec

end traversal
