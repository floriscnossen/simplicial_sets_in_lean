import algebraic_topology.simplex_category
import algebraic_topology.simplicial_set

open category_theory
open simplex_category
open_locale simplicial

-- def face {n : ℕ} : Π {m : ℕ} (f : [n] ⟶ [n+m]), Prop
-- | 0       f := (f = 𝟙 [n])
-- | (m + 1) f := ∃ (g: [n] ⟶ [n+m]) {i}, face g ∧ f = g ≫ δ i

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

inductive face {n : ℕ} : Π {m : ℕ}, ([n] ⟶ [m]) → Sort*
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
