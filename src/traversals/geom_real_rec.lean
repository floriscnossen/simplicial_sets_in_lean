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
  let colim := sSet_pushout (to_sSet_hom (δ e.t)) (bundle θ).2 in
  ⟨colim.cocone.X, to_sSet_hom (δ e.s) ≫ pushout_cocone.inl colim.cocone⟩

end geom_real_rec

def geom_real_rec {n} (θ : traversal n) : sSet := (geom_real_rec.bundle θ).1

namespace geom_real_rec
variables {n : ℕ}

def geom_real_incl (θ : traversal n) : Δ[n] ⟶ geom_real_rec θ := (geom_real_rec.bundle θ).2

def bundle_colim (e : edge n) (θ : traversal n) :=
  sSet_pushout (to_sSet_hom (δ e.t)) (bundle θ).2

@[simp]
lemma geom_real_rec_nil : geom_real_rec (⟦⟧ : traversal n) = Δ[n] := rfl

@[simp]
lemma geom_real_incl_nil : geom_real_incl (⟦⟧ : traversal n) = 𝟙 Δ[n] := rfl

lemma geom_real_rec_cons (e : edge n) (θ : traversal n) :
  geom_real_rec (e :: θ) = (bundle_colim e θ).cocone.X := rfl

lemma geom_real_incl_cons (e : edge n) (θ : traversal n) :
  geom_real_incl (e :: θ) = to_sSet_hom (δ e.s)
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

def k_rec_bundle : Π (θ θ' : traversal n),
  {k : geom_real_rec θ ⟶ 𝕋₁ // geom_real_incl θ ≫ k = simplex_as_hom (θ', θ)}
| ⟦⟧       θ' := ⟨simplex_as_hom (θ',⟦⟧), rfl⟩
| (e :: θ) θ' :=
begin
  let k_θ := k_rec_bundle θ (θ' ++ ⟦e⟧),
  refine ⟨(bundle_colim e θ).is_colimit.desc (pushout_cocone.mk _ k_θ.1 _), _⟩,
  { apply simplex_as_hom,
    --Special position
    exact (apply_map (σ e.1) θ' ++ ⟦(eˢ, e.2)⟧, (eᵗ, e.2) :: apply_map (σ e.1) θ)},
  change _ = geom_real_incl θ ≫ k_θ.val, rw k_θ.2,
  swap,
  rw [geom_real_incl_cons, category.assoc],
  rw [(bundle_colim e θ).is_colimit.fac _ walking_span.left, pushout_cocone.mk_ι_app_left],
  all_goals
  { rw [hom_comp_simplex_as_hom],
    rw simplex_as_hom_eq_iff,
    cases e with i b, cases b; simp;
    rw [𝕋₀_map_apply, 𝕋₀_map_apply, has_hom.hom.unop_op];
    simp[edge.s, edge.t, apply_map];
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
  a ++ b = c ++ d → {a' // c = a ++ a' ∧ b = a' ++ d} ⊕ {c' // a = c ++ c' ∧ d = c' ++ b} :=
begin
  induction c generalizing a,
  case nil { rw list.nil_append, rintro rfl, right, exact ⟨a, rfl, rfl⟩ },
  case cons : c cs ih {
    intro h, cases a,
    { left, use c :: cs, simpa using h },
    { simp at h, cases h, cases h_left, simp,
      exact ih h_right }}
end

section beta

variables {m : simplex_category} {α : m ⟶ [n]} {e : edge n} {θ₁ θ₂ : traversal m.len} (H : apply_map_to_edge α e = θ₁ ++ θ₂)

def β_conditions (i) (H : apply_map_to_edge α e = θ₁ ++ θ₂) :
  α.to_preorder_hom i < e.1 ∨ α.to_preorder_hom i > e.1 ∨ (i, e.2) ∈ θ₁ ∨ (i, e.2) ∈ θ₂ :=
begin
  cases lt_trichotomy (α.to_preorder_hom i) e.fst, left, exact h,
  cases h, swap, right, left, exact h,
  right, right,
  replace h : (α.to_preorder_hom (i, e.2).1, (i, e.2).2) = e, rw h, cases e, refl,
  rw [←edge_in_apply_map_to_edge_iff, H] at h, simp at h, exact h,
end

def β_fun (H : apply_map_to_edge α e = θ₁ ++ θ₂) : fin (m.len + 1) → fin ([n + 1].len + 1) := λ i,
  if h₁ : α.to_preorder_hom i < e.1 then (α.to_preorder_hom i).cast_succ
  else if h₂ : α.to_preorder_hom i > e.1 then (α.to_preorder_hom i).succ
  else if h₃ : (i, e.2) ∈ θ₁ then eˢ
  else eᵗ

lemma β_eq_es_iff (i) : β_fun H i = (eˢ) ↔ (i, e.2) ∈ θ₁ :=
begin
  simp[β_fun],
  split;
  intro h',
  { by_contra, split_ifs at h',
    rw [←fin.cast_succ_lt_cast_succ_iff, h'] at h_1,
    cases e with j b, cases b,
    exact lt_asymm (fin.cast_succ_lt_succ j) h_1,
    exact lt_irrefl _ h_1,
    rw [←fin.succ_lt_succ_iff, h'] at h_2,
    cases e with j b, cases b,
    exact lt_irrefl _ h_2,
    exact lt_asymm (fin.cast_succ_lt_succ j) h_2,
    cases e with j b, cases b,
    exact ne_of_lt (fin.cast_succ_lt_succ j) h',
    exact ne_of_gt (fin.cast_succ_lt_succ j) h' },
  { have hi : (i, e.2) ∈ apply_map_to_edge α e, rw H, exact list.mem_append_left θ₂ h',
    rw edge_in_apply_map_to_edge_iff at hi,
    cases e with j b, cases b;
    simp at hi h'; simp[hi, h'] }
end

lemma β_eq_et_iff (i) : β_fun H i = (eᵗ) ↔ (i, e.2) ∈ θ₂ :=
begin
  simp[β_fun],
  have hf: e.s = e.t ↔ false,
  { split; intro hf, cases e with j b, cases b,
    exact ne_of_lt (fin.cast_succ_lt_succ j) hf.symm,
    exact ne_of_lt (fin.cast_succ_lt_succ j) hf,
    exfalso, exact hf },
  split; intro h',
  { by_contra, split_ifs at h',
    rw [←fin.cast_succ_lt_cast_succ_iff, h'] at h_1,
    cases e with j b, cases b,
    exact lt_irrefl _ h_1,
    exact lt_asymm (fin.cast_succ_lt_succ j) h_1,
    rw [←fin.succ_lt_succ_iff, h'] at h_2,
    cases e with j b, cases b,
    exact lt_asymm (fin.cast_succ_lt_succ j) h_2,
    exact lt_irrefl _ h_2,
    cases e with j b, cases b,
    exact ne_of_gt (fin.cast_succ_lt_succ j) h',
    exact ne_of_lt (fin.cast_succ_lt_succ j) h',
    cases β_conditions i H, exact h_1 h_4,
    cases h_4, exact h_2 h_4,
    cases h_4, exact h_3 h_4,
    exact h h_4 },
  { have hi : (α.to_preorder_hom (i, e.2).1, (i, e.2).2) = e,
    { rw [←edge_in_apply_map_to_edge_iff, H], exact list.mem_append_right θ₁ h',  },
    cases e; simp at hi ⊢ h', simp [hi],
    have H' : sorted (θ₁ ++ θ₂), rw ←H, apply apply_map_to_edge_sorted,
    rw ←append_sorted_iff at H',
    intro hi', exfalso, have h'' := (H'.2.2 _ hi' _ h'),
    exact edge.lt_asymm _ _ h'' h'', }
end

lemma β_monotone : monotone (β_fun H) := λ i j hij,
begin
  simp [β_fun], split_ifs; try { apply le_refl },
  { exact α.to_preorder_hom.monotone hij },
  { apply le_of_lt, rw ←fin.le_cast_succ_iff, exact α.to_preorder_hom.monotone hij },
  { rw ←fin.cast_succ_lt_cast_succ_iff at h, cases e with j b, cases b,
    exact le_trans (le_of_lt h) (le_of_lt (fin.cast_succ_lt_succ _)),
    exact le_of_lt h },
  { rw ←fin.cast_succ_lt_cast_succ_iff at h, cases e with j b, cases b,
    exact le_of_lt h,
    exact le_trans (le_of_lt h) (le_of_lt (fin.cast_succ_lt_succ _)) },
  { refine absurd (α.to_preorder_hom.monotone hij) (not_le.mpr _),
    exact lt_of_lt_of_le h_2 (not_lt.mp h) },
  { simp, exact α.to_preorder_hom.monotone hij },
  { refine absurd (α.to_preorder_hom.monotone hij) (not_le.mpr _),
    exact lt_of_le_of_lt (not_lt.mp h_3) h_1 },
  { refine absurd (α.to_preorder_hom.monotone hij) (not_le.mpr _),
    exact lt_of_le_of_lt (not_lt.mp h_3) h_1 },
  all_goals { have hi := le_antisymm (not_lt.mp h) (not_lt.mp h_1) },
  { refine absurd (α.to_preorder_hom.monotone hij) (not_le.mpr _),
    rwa hi at h_3 },
  { cases e with k b, cases b; simp [edge.s, edge.t],
    exact le_of_lt h_4,
    apply le_of_lt, rw[←fin.le_cast_succ_iff], simp, exact le_of_lt h_4 },
  swap 3, swap 3,
  { refine absurd (α.to_preorder_hom.monotone hij) (not_le.mpr _),
    rwa hi at h_3 },
  { cases e with k b, cases b; simp [edge.s, edge.t],
    apply le_of_lt, rw[←fin.le_cast_succ_iff], simp, exact le_of_lt h_4,
    exact le_of_lt h_4 },
  all_goals
  { cases e with k b, cases b; dsimp[edge.s, edge.t];
    try { exact le_of_lt (fin.cast_succ_lt_succ k) },
    exfalso, have hj := le_antisymm (not_lt.mp h_4) (not_lt.mp h_3),
    have H' : sorted (θ₁ ++ θ₂), rw ←H, apply apply_map_to_edge_sorted,
    rw ←append_sorted_iff at H', },
  { have hj' : (α.to_preorder_hom (j, ∔).1, (j, ∔).2) = (k, ∔), simp, exact hj,
    rw [←edge_in_apply_map_to_edge_iff, H] at hj',
    simp [h_5] at hj' h_2,
    refine absurd hij (not_le.mpr _),
    exact H'.2.2 _ h_2 _ hj', },
  { have hi' : (α.to_preorder_hom (i, ∸).1, (i, ∸).2) = (k, ∸), simp, exact hi.symm,
    rw [←edge_in_apply_map_to_edge_iff, H] at hi',
    simp [h_2] at hi' h_5,
    refine absurd hij (not_le.mpr _),
    exact H'.2.2 _ h_5 _ hi', },
end

def β (H : apply_map_to_edge α e = θ₁ ++ θ₂) : m ⟶ [n+1] := hom.mk
{ to_fun    := β_fun H,
  monotone' := β_monotone H, }

lemma β_comp_σ : β H ≫ σ e.1 = α :=
begin
  ext1, ext1 i, simp [β, β_fun], split_ifs;
  simp [σ, fin.pred_above]; split_ifs; try { refl };
  try { push_neg at * },
  { exfalso, exact lt_asymm h h_1 },
  { exfalso, rw ←fin.le_cast_succ_iff at h_2, simp at h_2, exact h h_2 },
  { push_neg at h h_1, rw le_antisymm h_1 h, cases e with j b, cases b;
    simp[edge.s, edge.t] at h_3 ⊢,
    exfalso, exact h_3 },
  { push_neg at h h_1 h_3, rw le_antisymm h_1 h, cases e with j b, cases b;
    simp[edge.s, edge.t] at h_3 ⊢,
    exact absurd (fin.cast_succ_lt_succ j) (not_lt.mpr h_3) },
  { push_neg at h h_1, rw le_antisymm h_1 h, cases e with j b, cases b;
    simp[edge.s, edge.t] at h_3 ⊢,
    exfalso, exact h_3 },
  { push_neg at h h_1 h_3, rw le_antisymm h_1 h, cases e with j b, cases b;
    simp[edge.s, edge.t] at h_3 ⊢,
    exact absurd (fin.cast_succ_lt_succ j) (not_lt.mpr h_3) },
end

end beta


def geom_real_rec_lift' : Π (θ θ' : traversal n) {m} (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (geom_real_rec θ).obj (opposite.op m)
| ⟦⟧       θ' m α θ₁ θ₂ hθ := α
| (e :: θ) θ' m α θ₁ θ₂ hθ :=
  begin
    cases append_eq_append_split hθ with a' c',
    { rcases a' with ⟨θ₂', hθ₂', hθ₂⟩,
      let p : pushout_cocone _ _ := (bundle_colim e θ).cocone,
      apply p.inl.app (opposite.op m),
      exact β hθ₂',
    },
    { cases c' with c' hc',
      let p : pushout_cocone _ _ := (bundle_colim e θ).cocone,
      exact p.inr.app (opposite.op m) (geom_real_rec_lift' θ (θ' ++ ⟦e⟧) α c' θ₂ hc'.2.symm) },
  end

lemma geom_real_rec_fac_j' : Π (θ θ' : traversal n) {m} (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (j_rec θ).app (opposite.op m) (geom_real_rec_lift' θ θ' α θ₁ θ₂ hθ) = α
| ⟦⟧       θ' m α θ₁ θ₂ hθ := rfl
| (e :: θ) θ' m α θ₁ θ₂ hθ :=
  begin
    simp [geom_real_rec_lift'],
    cases append_eq_append_split hθ with a' c',
    { rcases a' with ⟨θ₂', H, hθ₂⟩,
      cases e with i b, simp,
      exact β_comp_σ H },
    { cases c' with c' hc',
      exact geom_real_rec_fac_j' θ (θ' ++ ⟦e⟧) α c' θ₂ _ }
  end

lemma geom_real_rec_fac_k' : Π (θ θ' : traversal n) {m} (α : m ⟶ [n]) (θ₁ θ₂ : traversal m.len) (hθ : θ₁ ++ θ₂ = apply_map α θ),
  (k_rec_bundle θ θ').1.app (opposite.op m) (geom_real_rec_lift' θ θ' α θ₁ θ₂ hθ) = ((apply_map α θ') ++ θ₁, θ₂)
| ⟦⟧       θ' m α θ₁ θ₂ hθ :=
  begin
    simp [apply_map] at hθ, cases hθ.1, cases hθ.2,
    simp[geom_real_rec_lift'], refl
  end
| (e :: θ) θ' m α θ₁ θ₂ hθ :=
  begin
    simp [geom_real_rec_lift'],
    cases append_eq_append_split hθ with a' c',
    { rcases a' with ⟨θ₂', H, hθ₂⟩,
      change (simplex_as_hom _).app (opposite.op m) (β H) = _,
      simp [simplex_as_hom],
      change apply_map _ _  = _ ∧ apply_map _ _  = _ ,
      rw [apply_map_append],
      simp [apply_map],
      rw [←apply_comp, ←apply_comp, β_comp_σ H],
      cases hθ₂,
      change _ ∧ _ = θ₂' ++ _,
      rw [list.append_left_inj],
      rw [list.append_right_inj],
      have h₁ : sorted (θ₁ ++ θ₂'), rw ←H, apply apply_map_to_edge_sorted,
      have h₂ := h₁, rw ←append_sorted_iff at h₂,
      split;
      refine eq_of_sorted_of_same_elem _ _ (apply_map_to_edge_sorted _ _) (by simp[h₂.1, h₂.2]) _;
      intro e'; rw edge_in_apply_map_to_edge_iff; simp; split; simp [β];
      try {rw β_eq_es_iff H}; try {rw β_eq_et_iff H}; intro h,
      { intro h', rw ←h' at h, simpa using h },
      { have he' : e' ∈ apply_map_to_edge α e, rw H, exact list.mem_append_left θ₂' h,
        rw edge_in_apply_map_to_edge_iff at he', cases e, cases e', simp at he' ⊢,
        cases he'.2, simp, exact h },
      { intro h', rw ←h' at h, simpa using h },
      { have he' : e' ∈ apply_map_to_edge α e, rw H, exact list.mem_append_right θ₁ h,
        rw edge_in_apply_map_to_edge_iff at he', cases e, cases e', simp at he' ⊢,
        cases he'.2, simp, exact h }},
    { cases c' with c' hc', simp,
      dsimp [k_rec, k_rec_bundle],
      change (k_rec_bundle θ (θ' ++ ⟦e⟧)).1.app (opposite.op m) (geom_real_rec_lift' θ (θ' ++ ⟦e⟧) α c' θ₂ _) = _,
      cases hc'.1,
      specialize geom_real_rec_fac_k' θ (θ' ++ ⟦e⟧) α c' θ₂ hc'.2.symm,
      rw [geom_real_rec_fac_k', apply_map_append], simp [apply_map], refl, }
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
| ⟦⟧ m α θ₁ θ₂ hθ x hx₁ hx₂ := by dsimp [geom_real_rec_lift]; rw ←hx₁; refl
| (e :: θ) m α ⟦⟧         θ₂ hθ x hx₁ hx₂ := sorry
| (e :: θ) m α (e₁ :: θ₁) θ₂ hθ x hx₁ hx₂ := sorry

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
