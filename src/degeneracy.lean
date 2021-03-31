import algebraic_topology.simplex_category
import algebraic_topology.simplicial_set

open category_theory
open simplex_category
open_locale simplicial

-- def degeneracy {n : ℕ} : Π {m : ℕ} (f : [n+m] ⟶ [n]), Prop
-- | 0       f := (f = 𝟙 [n])
-- | (m + 1) f := ∃ (g: [n+m] ⟶ [n]) {i}, degeneracy g ∧ f = σ i ≫ g

instance σ_split_epi {n} (i : fin (n+1)) : split_epi (σ i) := ⟨δ i.cast_succ, δ_comp_σ_self⟩

inductive degeneracy {n : ℕ} : Π {m : ℕ}, ([m] ⟶ [n]) → Sort*
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
