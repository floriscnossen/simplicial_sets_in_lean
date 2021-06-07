import traversals.basic

open category_theory
open category_theory.limits
open simplex_category
open sSet
open_locale simplicial

/-! # Geometric realisation of a traversal -/

namespace traversal

namespace geom_real

variables {n : ℕ} (θ : traversal n)

def s {n} : fin (n+1) × ± → fin (n+2)
| ⟨k, ∔⟩ := k.succ
| ⟨k, ∸⟩ := k.cast_succ

def t {n} : fin (n+1) × ± → fin (n+2)
| ⟨k, ∔⟩ := k.cast_succ
| ⟨k, ∸⟩ := k.succ

@[reducible]
def shape := fin(θ.length + 1) ⊕ fin(θ.length)

namespace shape

inductive hom :  shape θ → shape θ → Type*
| id (X)                 : hom X X
| s  (i : fin(θ.length)) : hom (sum.inl i.cast_succ) (sum.inr i)
| t  (i : fin(θ.length)) : hom (sum.inl i.succ)      (sum.inr i)

instance category : small_category (shape θ) :=
{ hom := hom θ,
  id := λ j, hom.id j,
  comp := λ j₁ j₂ j₃ f g,
  begin
    cases f, exact g,
    cases g, exact hom.s f_1,
    cases g, exact hom.t f_1,
  end,
  id_comp' := λ j₁ j₂ f, rfl,
  comp_id' := λ j₁ j₂ f, by cases f; refl,
  assoc'   := λ j₁ j₂ j₃ j₄ f g h,  by cases f; cases g; refl,
}

end shape

def diagram : shape θ ⥤ sSet :=
{ obj := λ j, sum.cases_on j (λ j, Δ[n]) (λ j, Δ[n+1]),
  map := λ _ _ f,
  begin
    cases f with _ j j,
    exact 𝟙 _,
    exact to_sSet_hom (δ (s (list.nth_le θ j.1 j.2))),
    exact to_sSet_hom (δ (t (list.nth_le θ j.1 j.2))),
  end,
  map_id'   := λ j, rfl,
  map_comp' := λ _ _ _ f g, by cases f; cases g; refl, }

-- @[simp]
-- lemma diagram_map_s {j} : (diagram θ).map (shape.hom.s j) = _ := sorry

def colimit : colimit_cocone (diagram θ) :=
{ cocone := combine_cocones (diagram θ) (λ n,
  { cocone := types.colimit_cocone _,
    is_colimit := types.colimit_cocone_is_colimit _ }),
  is_colimit := combined_is_colimit _ _,
}

end geom_real

def geom_real {n} (θ : traversal n) : sSet := (geom_real.colimit θ).cocone.X

namespace geom_real

variables {n : ℕ} (θ : traversal n)

def geom_real_cocone_mk
(X   : sSet)
(fst : fin(θ.length + 1) → (Δ[n] ⟶ X))
(snd : fin(θ.length) → (Δ[n+1] ⟶ X))
(s_comp_snd  : ∀ j : fin(θ.length),
  standard_simplex.map (δ (s (list.nth_le θ j.1 j.2))) ≫ snd j = fst j.cast_succ)
(t_comp_snd  : ∀ j : fin(θ.length),
  standard_simplex.map (δ (t (list.nth_le θ j.1 j.2))) ≫ snd j = fst j.succ)
: limits.cocone (diagram θ) :=
{ X := X,
  ι :=
  { app := λ j, sum.cases_on j (λ j, fst j) (λ j, snd j),
    naturality' := λ _ _ f,
    begin
      cases f with _ j j, refl,
      all_goals
      { change standard_simplex.map (δ _) ≫ snd j = fst _ ≫ 𝟙 X,
        rw category.comp_id, },
      exact s_comp_snd j,
      exact t_comp_snd j,
    end }}

def j_cocone : limits.cocone (diagram θ) :=
{ X := Δ[n],
  ι :=
  { app := λ j,
    begin
      cases j,
      exact 𝟙 _,
      exact to_sSet_hom (σ (list.nth_le θ j.1 j.2).1),
    end,
    naturality' := λ _ _ f,
    begin
      cases f with _ j j,
      { refl },
      all_goals
      { change standard_simplex.map (δ _) ≫ standard_simplex.map (σ _) = 𝟙 _,
        rw [←standard_simplex.map_comp, ←standard_simplex.map_id],
        apply congr_arg,
        cases list.nth_le θ _ _, cases snd, },
      exact δ_comp_σ_succ,
      exact δ_comp_σ_self,
      exact δ_comp_σ_self,
      exact δ_comp_σ_succ,
    end }
}

-- def j_cocone' : limits.cocone (diagram θ) :=
-- { X := Δ[n],
--   ι :=
--   { app := λ i, match i with
--     | (sum.inl j) := 𝟙 _
--     | (sum.inr j) := to_sSet_hom (σ (list.nth_le θ j.1 j.2).1)
--     end,
--     naturality' := λ j₁ j₂ f, match j₁, j₂, f with
--     | j₁, j₂, (shape.hom.id) := sorry
--     end
--     begin
--       cases j₁; cases j₂; cases f,
--       refl, swap 3, refl,
--       all_goals
--       { change standard_simplex.map (δ _) ≫ standard_simplex.map (σ _) = 𝟙 _,
--         rw [←standard_simplex.map_comp, ←standard_simplex.map_id],
--         apply congr_arg,
--         cases list.nth_le θ _ _, cases snd, },
--       exact δ_comp_σ_succ,
--       exact δ_comp_σ_self,
--       exact δ_comp_σ_self,
--       exact δ_comp_σ_succ,
--     end }
-- }

def j_map : geom_real θ ⟶ Δ[n] :=
  (colimit θ).is_colimit.desc (j_cocone θ)

lemma apply_δ_self {n} (i : fin (n + 2)) (b : ±) : apply_map (δ i) ⟦(i, b)⟧ = ⟦⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  exact apply_map_preserves_sorted _ _ (list.sorted_singleton (i, b)),
  exact list.sorted_nil,
  intro e, cases e,
  rw edge_in_apply_map_iff, simp,
  intro h, exfalso,
  simp [δ, fin.succ_above] at h,
  split_ifs at h,
  finish,
  rw [not_lt, fin.le_cast_succ_iff] at h_1, finish,
end

lemma apply_δ_succ_cast_succ {n} (i : fin (n + 1)) (b : ±) :
  apply_map (δ i.succ) ⟦(i.cast_succ, b)⟧ = ⟦(i, b)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  exact apply_map_preserves_sorted _ _ (list.sorted_singleton (i.cast_succ, b)),
  exact list.sorted_singleton (i, b),
  intro e, cases e,
  rw edge_in_apply_map_iff, simp, intro hb, cases hb,
  split,
  { intro he,
    have H : (δ i.succ ≫ σ i).to_preorder_hom e_fst = (σ i).to_preorder_hom i.cast_succ,
    { rw ←he, simp, },
    rw δ_comp_σ_succ at H,
    simpa [σ, fin.pred_above] using H, },
  { intro he, cases he,
    simp [δ, fin.succ_above, fin.cast_succ_lt_succ], }
end

lemma apply_δ_cast_succ_succ {n} (i : fin (n + 1)) (b : ±) :
  apply_map (δ i.cast_succ) ⟦(i.succ, b)⟧ = ⟦(i, b)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  exact apply_map_preserves_sorted _ _ (list.sorted_singleton (i.succ, b)),
  exact list.sorted_singleton (i, b),
  intro e, cases e,
  rw edge_in_apply_map_iff, simp, intro hb, cases hb,
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

def k_cocone : cocone (diagram θ) :=
{ X := 𝕋₁,
  ι :=
  { app := λ j,
    begin
      cases j,
      exact (θ.add_point j).as_hom,
      apply pointed_traversal.as_hom,
      cases list.nth_le θ j.cast_succ.1 j.2 with i b,
      let σθ' : pointed_traversal (n+1) := 𝕋₁.map (σ i).op (θ.add_point_remove j),
      cases b,
      --Special position
      exact (σθ'.1 ++ ⟦(i.succ, ∔)⟧,      (i.cast_succ, ∔) :: σθ'.2),
      exact (σθ'.1 ++ ⟦(i.cast_succ, ∸)⟧, (i.succ, ∸)      :: σθ'.2),
    end,
    naturality' := λ _ _ f,
    begin
      cases f with _ j j,
      refl,
      { change to_sSet_hom (_) ≫ simplex_as_hom _ = (θ.add_point j.cast_succ).as_hom,
        rw [add_point_cast_succ, hom_comp_simplex_as_hom], apply congr_arg,
        cases list.nth_le θ j.cast_succ.1 j.2 with i b, cases b; simp;
        rw [𝕋₀_map_apply, 𝕋₀_map_apply, 𝕋₀_map_apply, 𝕋₀_map_apply, apply_map_append];
        rw [←apply_comp, has_hom.hom.unop_op, has_hom.hom.unop_op];
        simp only [s, δ_comp_σ_self, δ_comp_σ_succ, apply_id, types_id_apply];
        rw apply_δ_self;
        rw [←list.nil_append (θ.add_point_remove j).snd, ←list.nil_append (apply_map (σ i) _)];
        rw [←list.cons_append, ←list.cons_append, apply_map_append, ←apply_comp];
        simp only [δ_comp_σ_succ, δ_comp_σ_self, @apply_id [n], types_id_apply];
        simp [apply_δ_succ_cast_succ, apply_δ_cast_succ_succ], },
      { change to_sSet_hom (_) ≫ simplex_as_hom _ = (θ.add_point j.succ).as_hom,
        rw [add_point_succ, hom_comp_simplex_as_hom], apply congr_arg,
        cases list.nth_le θ j.cast_succ.1 j.2 with i b, cases b; simp;
        rw [𝕋₀_map_apply, 𝕋₀_map_apply, 𝕋₀_map_apply, 𝕋₀_map_apply, apply_map_append];
        rw [←apply_comp, has_hom.hom.unop_op, has_hom.hom.unop_op];
        simp only [t, δ_comp_σ_self, δ_comp_σ_succ, apply_id, types_id_apply];
        simp only [apply_δ_succ_cast_succ, apply_δ_cast_succ_succ];
        rw [←list.nil_append (θ.add_point_remove j).snd, ←list.nil_append (apply_map (σ i) _)];
        rw [←list.cons_append, apply_map_append, ←apply_comp];
        simp only [δ_comp_σ_succ, δ_comp_σ_self, @apply_id [n], types_id_apply];
        simp [apply_δ_self], },
    end }
}

def k_map : geom_real θ ⟶ 𝕋₁ := (colimit θ).is_colimit.desc (k_cocone θ)

lemma apply_σ_to_plus {n} (i : fin (n + 1)) :
  apply_map (σ i) ⟦(i, ∔)⟧ = ⟦(i.succ, ∔), (i.cast_succ, ∔)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_preserves_sorted,
    apply list.sorted_singleton,},
  { simp [sorted], intros a b ha hb, rw ha, rw hb,
    exact fin.cast_succ_lt_succ i, },
  { intro e, cases e with l b,
    rw edge_in_apply_map_iff,
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

lemma apply_σ_to_min {n} (i : fin (n + 1)) :
  apply_map (σ i) ⟦(i, ∸)⟧ = ⟦(i.cast_succ, ∸), (i.succ, ∸)⟧ :=
begin
  apply eq_of_sorted_of_same_elem,
  { apply apply_map_preserves_sorted,
    apply list.sorted_singleton,},
  { simp[sorted],
    intros a b ha hb, rw [ha, hb],
    exact fin.cast_succ_lt_succ i, },
  { intro e, cases e with l b,
    rw edge_in_apply_map_iff,
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

def geom_real_pullback_cone {n} (θ : traversal n) : pullback_cone (θ.as_hom) cod :=
  pullback_cone.mk (j_map θ) (k_map θ)
begin
  apply (geom_real.colimit θ).is_colimit.hom_ext,
  intro i,
  simp [j_map, k_map],
  cases i,
  { change simplex_as_hom _ = simplex_as_hom _ ≫ _,
    rw simplex_as_hom_comp_hom,
    rw simplex_as_hom_eq_iff,
    exact symm (add_point_comp _ _), },
  { change to_sSet_hom _ ≫ simplex_as_hom _ = simplex_as_hom _ ≫ _,
    rw [hom_comp_simplex_as_hom, simplex_as_hom_comp_hom],
    rw simplex_as_hom_eq_iff,
    change apply_map (σ _) θ = _,
    rw congr_arg (apply_map (σ _)) (add_point_remove_comp θ i).symm,
    cases list.nth_le θ i.1 i.2 with l b,
    cases b; simp;
    change _ = apply_map (σ l) _ ++ _ ++ _ :: apply_map (σ l) _; simp,
    all_goals
    { suffices H : _ = apply_map (σ l) _ ++ ⟦_, _⟧ ++ apply_map (σ l) _,
      { simpa using H, },
      try {rw ←apply_σ_to_plus},
      try {rw ←apply_σ_to_min},
      simp [apply_map], }}
end

@[simps]
def pullback_cone_nil (n) : pullback_cone (as_hom ⟦⟧) cod :=
  pullback_cone.mk (to_sSet_hom (𝟙 [n])) (simplex_as_hom (⟦⟧, ⟦⟧))
begin
  dsimp [as_hom],
  rw [hom_comp_simplex_as_hom, simplex_as_hom_comp_hom],
  rw simplex_as_hom_eq_iff,
  simp[𝕋₀_map_apply, apply_map, cod],
end

def pullback_cone_nil_is_limit (n) : is_limit (pullback_cone_nil n) :=
  evaluation_jointly_reflects_limits (pullback_cone_nil n) (λ m,
begin
  dsimp[evaluation, map_cone],
  change is_limit (pullback_cone _ _),
  refine pullback_cone.is_limit_aux _ _ _ _ _,
  intro t, exact pullback_cone.fst t,
  { change t.fst ≫ to_sSet_hom (𝟙 [n]) = t.fst,
    rw [to_sSet_hom_id, category.comp_id'] },
  { change t.fst ≫ simplex_as_hom _ = t.snd,
    rw [category.comp_id'] },
  all_goals { simp [pullback_cone_nil n] },
  --  (λ t, t.fst)
end)

lemma geom_real_nil_iso_Δn : geom_real_pullback_cone ⟦⟧ ≅ pullback_cone_nil n :=
{ hom := sorry,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry
  }

theorem geom_real_is_pullback_θ_cod : is_limit (geom_real_pullback_cone θ) :=
  evaluation_jointly_reflects_limits (geom_real_pullback_cone θ) (λ m,
begin

end)

-- noncomputable
-- def lift_of_lift_representable {J : Type*} [small_category J] {F : J ⥤ sSet}
-- (t : cone F)
-- (lift_rep : Π n, Δ[n] ⟶ t.X) :
--   Π (s : cone F), s.X ⟶ t.X := λ s,
-- begin
--   -- change (cocone_of_representable s.X).X ⟶ t.X,
--   refine (colimit_of_representable s.X).desc ⟨t.X, _⟩,
--   exact
--   { app         := λ X, sorry,
--     naturality' := sorry}
-- end

-- noncomputable
-- def lift_of_lift_representable' {J : Type*} [small_category J] {F : J ⥤ sSet}
-- (t : cone F)
-- (lift_rep : Π n, Δ[n] ⟶ t.X) :
--   Π (s : cone F), s.X ⟶ t.X := λ s,
-- begin
--   -- change (cocone_of_representable s.X).X ⟶ t.X,
--   refine (colimit_of_representable s.X).desc ⟨t.X, _⟩,
--   exact
--   { app         := λ X, sorry,
--     naturality' := sorry}
-- end

-- def pullback_θ_cod : limit_cone (cospan (θ.as_hom) cod) :=
-- { cone := combine_cones (cospan (θ.as_hom) cod) (λ n,
--   { cone := types.limit_cone _,
--     is_limit := types.limit_cone_is_limit _ }),
--   is_limit := combined_is_limit _ _, }

-- lemma geom_real_equiv_pullback_θ_cod : geom_real θ ≅ (pullback_θ_cod θ).cone.X :=
--   nat_iso.of_components (λ m,
--   { hom := ((pullback_θ_cod θ).is_limit.lift (pullback_cone θ)).app m,
--     inv := sorry,
--     hom_inv_id' :=
--     begin
--       sorry,
--     end,
--     inv_hom_id' :=
--     begin
--       sorry
--     end})
--   ((pullback_θ_cod θ).is_limit.lift (pullback_cone θ)).naturality

-- -- is_limit_aux
-- lemma geom_real_is_pullback_θ_cod : is_limit (pullback_cone θ) :=
-- { lift  := λ c,
--   { app         := λ m x,
--     begin
--       rw [←m.op_unop, ←m.unop.mk_len] at x,
--       change limits.pullback_cone θ.as_hom cod at c,
--       let α := simplex_as_hom x ≫ c.snd,
--       simp [pullback_cone],
--       sorry
--     end,
--     naturality' := sorry},
--   fac'  := sorry,
--   uniq' := sorry }

-- lemma geom_real_is_pullback_θ_cod' : is_limit (pullback_cone θ) :=
-- begin
--   apply pullback_cone.is_limit_aux (pullback_cone θ)
--   (λ c, ((pullback_θ_cod θ).is_limit.lift c) ≫ (geom_real_equiv_pullback_θ_cod θ).inv);
--   intros c; simp,
-- end
-- (λ c, ((pullback_θ_cod θ).is_limit.lift c) ≫ (geom_real_equiv_pullback_θ_cod θ).inv)
-- (sorry)

-- { lift  := λ c, ((pullback_θ_cod θ).is_limit.lift c) ≫ (geom_real_equiv_pullback_θ_cod θ).inv,
--   fac'  := λ c j,
--   begin
--     simp,
--     suffices H : _ = (pullback_θ_cod θ).is_limit.lift c ≫ _,
--     -- change _ = (pullback_θ_cod θ).is_limit.lift c ≫ _,
--     rw [(pullback_θ_cod θ).is_limit.fac],
--     rw (geom_real_equiv_pullback_θ_cod θ).inv.naturality,
--   end,
--   uniq' := sorry }

-- def Δn_inclusion

-- lemma geom_real_of_nil : geom_real (list.nil : traversal n) ≅ Δ[n] := sorry



-- def lift_repr {m} (α : [m] ⟶ [n]) {θ₁ θ₂ : traversal m} (hθ : θ₁ ++ θ₂ = apply_map α θ) :
--   (geom_real θ).obj (opposite.op [m]) :=
-- begin
--   induction θ; simp [apply_map] at hθ,
--   { exact (@geom_real_of_nil n).inv.app (opposite.op [m]) α },

-- end

end geom_real

end traversal
