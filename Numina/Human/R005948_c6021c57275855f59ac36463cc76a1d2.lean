import Mathlib 

open Real Filter Topology 

namespace calculus_610862 

theorem arctan_sub {x y : ℝ} (h : x * (- y) < 1) : 
    arctan x - arctan y = arctan ((x - y) / (1 + x * y)) := by 
  rw [show arctan x - arctan y = arctan x + (- arctan y) by rfl] 
  rw [← arctan_neg, arctan_add h] 
  congr 
  ring  

theorem tendsto_arctan_nat_atTop : Tendsto (fun n : ℕ ↦ arctan n) atTop (nhds (π / 2)) := by
  have h_comp_limit : Tendsto (fun n : ℕ => arctan (n : ℝ)) atTop (𝓝[<] (π / 2)) := 
    tendsto_arctan_atTop.comp tendsto_natCast_atTop_atTop 
  exact Tendsto.mono_right h_comp_limit nhdsWithin_le_nhds

@[pp_nodot]
noncomputable def arccot (x : ℝ) : ℝ := π / 2 - arctan x

lemma arccot_eq_pi_div_two_sub_arctan (x : ℝ) : arccot x = π / 2 - arctan x := rfl

lemma arccot_pos (x : ℝ) : 0 < arccot x := by 
  rw [arccot_eq_pi_div_two_sub_arctan]
  simp only [sub_pos]
  exact arctan_lt_pi_div_two x 
 
lemma arccot_eq_arctan_inv {x : ℝ} (hx : 0 < x) : arccot x = arctan (1 / x) := by 
  rw [arccot_eq_pi_div_two_sub_arctan]
  simp [arctan_inv_of_pos hx] 

lemma arccot_telescoping_identity (n : ℕ) : arccot (n ^ 2 + n + 1) = arctan (n + 1) - arctan n := by
  match n with
  | 0 => simp [arccot_eq_pi_div_two_sub_arctan] ; ring
  | n + 1 =>
    rw [arccot_eq_arctan_inv]
    · rw [arctan_sub]
      congr 1
      · rify
        field_simp
        ring
      · calc
           ((↑(n + 1) + 1) * -↑(n + 1) : ℝ) < 0 := by
            simp only [Nat.cast_add, Nat.cast_one, neg_add_rev]
            apply mul_neg_of_pos_of_neg
            · norm_cast
              simp
            · simp only [add_neg_lt_iff_lt_add, zero_add]
              calc
                _ < (0 : ℝ) := by simp
                _ ≤  _ := Nat.cast_nonneg' n
          _ < 1 := by norm_num
    · norm_cast
      apply add_pos
      <;> norm_num

end calculus_610862 

open calculus_610862 

/-Evaluate $\sum_{n=0}^{\infty} \cot ^{-1}\left(n^{2}+n+1\right)$.-/
theorem calculus_610862 : HasSum (fun (n : ℕ) => arccot (n ^ 2 + n + 1)) (π / 2) := by 
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have h : (fun n ↦ ∑ i ∈ Finset.range n, arccot (↑i ^ 2 + ↑i + 1)) = (fun n : ℕ  ↦ arctan n - arctan (0 : ℕ)) := by
      ext n 
      conv => enter [1, 2, i] ; rw [arccot_telescoping_identity]
      let f := fun n : ℕ ↦ arctan ↑n 
      convert_to ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
      · simp [f] 
      rw [Finset.sum_range_tsub]
      -- $\sum_{n=0}^{\infty} \cot \left(n^{2}+n+1\right)=
      -- \sum_{n=0}^{\infty} \arctan \left(\frac{1}{n^{2}+n+1}\right)=
      -- \sum_{n=0}^{\infty} \arctan (n+1)-\arctan (n)$ by the sum/difference formula for tangent. 
      · simp [f] 
        intro x y hxy 
        rify at hxy 
        simp only [f]
        exact arctan_le_arctan hxy 
    rw [h] 
    -- This sum, taken out to $n=N$, telescopes to $-\arctan (0)+\arctan (N+1)$. 
    simp only [CharP.cast_eq_zero, arctan_zero, sub_zero]
    exact tendsto_arctan_nat_atTop
    -- So as $N$ goes to infinity, the sum goes to $\pi / 2$.
  · intro i 
    exact (arccot_pos _).le 



