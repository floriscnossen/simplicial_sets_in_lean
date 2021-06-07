import traversals.basic

open category_theory
open category_theory.limits
open simplex_category
open sSet
open_locale simplicial

namespace traversal

namespace geom_real_rec

variables {n : ℕ}

def s : fin (n+1) × ± → fin (n+2)
| ⟨k, ∔⟩ := k.succ
| ⟨k, ∸⟩ := k.cast_succ

def t : fin (n+1) × ± → fin (n+2)
| ⟨k, ∔⟩ := k.cast_succ
| ⟨k, ∸⟩ := k.succ

-- inductive shape : Type
-- | left  : shape
-- | mid   : shape
-- | right : shape
-- | tail  : shape

-- namespace shape

-- inductive hom : shape → shape → Type
-- | id (X) : hom X X
-- | s      : hom left  mid
-- | t      : hom right mid
-- | incl   : hom right tail

-- instance category : small_category shape :=
-- { hom := hom,
--   id := λ j, hom.id j,
--   comp := λ j₁ j₂ j₃ f g,
--   begin
--     cases f, exact g,
--     cases g, exact hom.s,
--     cases g, exact hom.t,
--     cases g, exact hom.incl,
--   end,
--   id_comp' := λ j₁ j₂ f, rfl,
--   comp_id' := λ j₁ j₂ f, by cases f; refl,
--   assoc'   := λ j₁ j₂ j₃ j₄ f g h, by cases f; cases g; refl,
-- }

-- end shape

-- def combine_cocones_types
-- (sh : Type*) (c : small_category sh)
-- (diag : sh ⥤ sSet) :
--   colimit_cocone (diag) :=
-- { cocone := combine_cocones (diag) (λ n,
--   { cocone := types.colimit_cocone _,
--     is_colimit := types.colimit_cocone_is_colimit _ }),
--   is_colimit := combined_is_colimit _ _,
-- }

-- def geom_real_bundle (θ : traversal n) : Σ (g : sSet), Δ[n] ⟶ g :=
-- begin
--   induction θ with e θ θ_ih,
--   { exact ⟨Δ[n], 𝟙 _⟩ },
--   let g := combine_cocones_types shape shape.category
--   { obj := λ p, shape.cases_on p Δ[n] Δ[n+1] Δ[n] θ_ih.1,
--     map := λ p q f,
--     begin
--       cases f,
--       exact 𝟙 _,
--       exact to_sSet_hom (δ (s e)),
--       exact to_sSet_hom (δ (t e)),
--       exact θ_ih.2
--     end,
--     map_id'   := λ j, rfl,
--     map_comp' := λ _ _ _ f g,
--     begin
--       cases f; cases g; try {refl},
--       rw category.id_comp, refl,
--       rw category.comp_id, refl,
--     end },
--   exact ⟨g.cocone.X, g.cocone.ι.app shape.left⟩,
-- end

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
  let colim := sSet_pushout (to_sSet_hom (δ (t e))) (bundle θ).2 in
  -- let colim := sSet_colimit (span (to_sSet_hom (δ (t e))) (bundle θ).2) in
  ⟨colim.cocone.X, to_sSet_hom (δ (s e)) ≫ pushout_cocone.inl colim.cocone⟩

end geom_real_rec

def geom_real_rec {n} (θ : traversal n) : sSet := (geom_real_rec.bundle θ).1

namespace geom_real_rec
variables {n : ℕ}

def geom_real_incl (θ : traversal n) : Δ[n] ⟶ geom_real_rec θ := (geom_real_rec.bundle θ).2

def bundle_colim (e : edge n) (θ : traversal n) :=
  sSet_colimit (span (to_sSet_hom (δ (t e))) (bundle θ).2)

@[simp]
lemma bundle_nil : bundle ⟦⟧ = ⟨Δ[n], 𝟙 _⟩ := rfl

lemma geom_real_rec_eq (e : edge n) (θ : traversal n) :
  geom_real_rec (e :: θ) = (bundle_colim e θ).cocone.X := rfl

lemma geom_real_incl_eq (e : edge n) (θ : traversal n) :
  geom_real_incl (e :: θ) = to_sSet_hom (δ (s e)) ≫ pushout_cocone.inl (bundle_colim e θ).cocone := rfl


def j_rec_bundle : Π (θ : traversal n),
  {j : geom_real_rec θ ⟶ Δ[n] // geom_real_incl θ ≫ j = 𝟙 Δ[n]}
| ⟦⟧       := ⟨𝟙 Δ[n], category.comp_id (𝟙 Δ[n])⟩
| (e :: θ) :=
begin
  let j_θ := j_rec_bundle θ,
  refine ⟨(bundle_colim e θ).is_colimit.desc (pushout_cocone.mk (to_sSet_hom (σ (e).1)) j_θ.1 _), _⟩,
  change _ = geom_real_incl θ ≫ j_θ.val, rw j_θ.2,
  swap,
  rw [geom_real_incl_eq, category.assoc],
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

@[simp] lemma apply_δ_self {n} (i : fin (n + 2)) (b : ±) : apply_map_to_edge (δ i) (i, b) = ⟦⟧ :=
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
  {k : geom_real_rec θ ⟶ 𝕋₁ // geom_real_incl θ ≫ k = pointed_traversal.as_hom (θ', θ)}
| ⟦⟧       θ' := ⟨pointed_traversal.as_hom (θ',⟦⟧), rfl⟩
| (e :: θ) θ' :=
begin
  let k_θ := k_rec_bundle θ (θ' ++ ⟦e⟧),
  refine ⟨(bundle_colim e θ).is_colimit.desc (pushout_cocone.mk _ k_θ.1 _), _⟩,
  { apply pointed_traversal.as_hom,
    cases e with i b, cases b,
    --Special position
    exact (apply_map (σ i) θ' ++ ⟦(i.succ, ∔)⟧,      (i.cast_succ, ∔) :: apply_map (σ i) θ),
    exact (apply_map (σ i) θ' ++ ⟦(i.cast_succ, ∸)⟧, (i.succ, ∸)      :: apply_map (σ i) θ) },
  change _ = geom_real_incl θ ≫ k_θ.val, rw k_θ.2,
  swap,
  rw [geom_real_incl_eq, category.assoc],
  rw [(bundle_colim e θ).is_colimit.fac _ walking_span.left, pushout_cocone.mk_ι_app_left],
  all_goals
  { dsimp [pointed_traversal.as_hom],
    rw [hom_comp_simplex_as_hom],
    rw simplex_as_hom_eq_iff,
    cases e with i b, cases b; simp;
    rw [𝕋₀_map_apply, 𝕋₀_map_apply, has_hom.hom.unop_op];
    simp[s, t, apply_map];
    rw [←apply_comp, ←apply_comp];
    try { rw δ_comp_σ_self }; try { rw δ_comp_σ_succ };
    rw [apply_id, apply_id];
    simp },
end

def k_rec (θ : traversal n) : geom_real_rec θ ⟶ 𝕋₁ := (k_rec_bundle θ ⟦⟧).1

def k_prop (θ : traversal n) :
  geom_real_incl θ ≫ k_rec θ = pointed_traversal.as_hom (⟦⟧, θ) := (k_rec_bundle θ ⟦⟧).2

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

theorem geom_real_is_pullback_θ_cod (θ : traversal n) : is_limit (pullback_cone_rec θ) :=
begin
  apply evaluation_jointly_reflects_limits,
  intro m, exact
  { lift  := λ c,
    begin
      -- change
      sorry,
    end,
    fac'  := sorry,
    uniq' := sorry }
end

-- lemma cospan_comp_eval {X Y Z : sSet} (f : X ⟶ Z) (g : Y ⟶ Z) {m} :
--   cospan f g ⋙ (evaluation simplex_categoryᵒᵖ Type).obj m = cospan (f.app m) (g.app m) :=
-- begin
--   dsimp [cospan],
-- end

theorem geom_real_is_pullback_θ_cod_rec : Π (θ : traversal n), is_limit (pullback_cone_rec θ)
| ⟦⟧       :=
begin
  apply evaluation_jointly_reflects_limits,
  intro m,
  suffices H : is_limit (((yoneda_pairing simplex_category).obj m).map_cone (pullback_cone_rec list.nil)),

  exact
  { lift  := λ c,
    begin
      rw ←pullback_cone.of_cone_X,
      let d := pullback_cone.of_cone c, change d.X ⟶ _,
      simp at d,
      let d_fst := d.fst, let d_snd := d.snd, simp at d_snd d_fst,
      intro x,
      simp [pullback_cone_rec, geom_real_rec],
      -- let α := d_fst x,
      sorry,
    end,
    fac'  := sorry,
    uniq' := sorry }
end
| (e :: θ) :=
begin
  apply evaluation_jointly_reflects_limits,
  intro m, exact
  { lift  := λ c,
    begin
      -- change
      sorry,
    end,
    fac'  := sorry,
    uniq' := sorry }
end

end geom_real_rec

end traversal
