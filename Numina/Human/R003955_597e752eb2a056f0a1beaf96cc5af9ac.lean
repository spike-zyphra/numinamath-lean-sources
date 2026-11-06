import Mathlib

-- the following lemma is the Bernoulli inequality multiplying by a positive number both sides
lemma bernoulli_inequality_mul_right {s : ℝ} (hs : s ≥ -1) {a : ℝ} (ha : a ≥ 1) {b : ℝ} (hb : b ≥ 0) :
    b * (1 + a * s) ≤ b * ((1 + s) ^ a) := by 
  exact mul_le_mul_of_nonneg_left (one_add_mul_self_le_rpow_one_add hs ha) hb 

-- the following lemma is the strict Bernoulli inequality multiplying by a positive number both sides
lemma strict_bernoulli_inequality_mul_right {s : ℝ} (hs : s ≥ -1) (hs' : s ≠ 0) {a : ℝ} (ha : a > 1) {b : ℝ} (hb : b > 0) :
    b * (1 + a * s) < b * ((1 + s) ^ a) := by
  exact mul_lt_mul_of_pos_left (one_add_mul_self_lt_rpow_one_add hs hs' ha) hb    

theorem inequalities_224873 {A B : ℝ} {p q : ℚ} (hp : p ≠ 0) (hq : q ≠ 0) 
(h : A > 0 ∧ B > 0) (h1 : 1 / p + 1 / q = 1) (h2 : p > 0 ∧ q > 0) : 
    (p > 1 → A ^ ((1 : ℝ) / p) * B ^ ((1 : ℝ) / q) ≤ A / p + B / q) ∧ 
    (p < 1 → A ^ ((1 : ℝ) / p) * B ^ ((1 : ℝ) / q) ≥ A / p + B / q) ∧ 
    (A ≠ B → (p > 1 → A ^ ((1 : ℝ) / p) * B ^ ((1 : ℝ) / q) < A / p + B / q) ∧ 
    (p < 1 → A ^ ((1 : ℝ) / p) * B ^ ((1 : ℝ) / q) > A / p + B / q)) := by 
  rify at h1
  have rw_conj_exp : 1 / (q : ℝ) = 1 - 1 / p := by linarith
  constructor
  --if p > 1 then A ^ (1 / p) * B ^ (1 / q) ≤ A / p + B / q
  · intro hpgt
    have p_conj_q : (p : ℝ).IsConjExponent (q : ℝ) := by
      refine ⟨?_, ?_⟩
      norm_cast
      rw[← one_div, ← one_div]
      exact h1
    --this is true by Young's inequality a * b ≤ a / p + b / q, with a = A ^ (1 / p) and b = B ^ (1 / q)
    have young := @Real.young_inequality_of_nonneg (A ^ ((1 / p) : ℝ)) (B ^ ((1 / q) : ℝ)) p q (Real.rpow_nonneg (le_of_lt h.1) (1 / p : ℝ)) (Real.rpow_nonneg (le_of_lt h.2) (1 / q : ℝ)) p_conj_q
    --by algebraic manipulation we obtain the desired inequality
    rw[← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)] at young
    rw[div_mul, div_mul] at young
    rify at hp hq
    rw[div_self hp, div_self hq] at young
    norm_num at young
    rw[one_div, one_div]
    exact young
  · constructor
    --if p < 1 then A ^ (1 / p) * B ^ (1 / q) ≥ A / p + B / q
    · intro hplt
      let s := A/B - 1
      let a := 1 / (p : ℝ)
      have den_bound : s ≥ -1 := by 
        have : A/B > 0 := by exact div_pos h.1 h.2
        simp[s]
        linarith
      have exp_bound : a ≥ 1 := by 
        simp[a]
        field_simp
        rw[le_one_div (by linarith) (by norm_cast; exact h2.1)]
        norm_num
        norm_cast
        exact le_of_lt hplt
      --this is true by Bernoulli's inequality above, multiplying both sides by B
      have bernoulli := bernoulli_inequality_mul_right den_bound exp_bound (le_of_lt h.2)
      --the lhs becomes A ^ (1 / p) * B ^ (1 / q) after algebraic manipulation
      have lhs : A ^ (1 / p : ℝ) * B ^ (1 / q : ℝ) = B * (1 + s) ^ a := by 
          simp only [s, a]
          norm_num
          rw[Real.div_rpow (le_of_lt h.1) (le_of_lt h.2)]
          rw[← mul_div_assoc, mul_comm B, mul_div_assoc]
          nth_rw 2 [← Real.rpow_one B]
          rw[← Real.rpow_sub h.2]
          field_simp
          left
          rw[sub_div, div_self (by norm_cast)]
          rw[← rw_conj_exp]
      --the rhs becomes A / p + B / q after algebraic manipulation
      have rhs : A / p + B / q = B * (1 + a * s) := by 
          simp only [s, a]
          rw[mul_sub, mul_add, mul_sub]
          rw[← mul_assoc]
          nth_rw 2 [mul_comm B]
          rw[mul_assoc, ← mul_div_assoc, mul_comm B A, mul_div_assoc, div_self (by linarith)]
          rw[add_sub, add_comm (B * 1), ← add_sub]
          rw[← mul_sub B 1 (1 / (p : ℝ) * 1)]
          rw[mul_one, mul_one, ← rw_conj_exp]
          ring_nf
      --this yields the desired inequality
      rw[← lhs, ← rhs] at bernoulli
      exact bernoulli
    · intro hAnB
      constructor
      --if A ≠ B and p > 1 then A ^ (1 / p) * B ^ (1 / q) < A / p + B / q
      · intro hpgt
        have one_div_p_lt : 0 < 1 / (p : ℝ) ∧ 1 / (p : ℝ) < 1 := by 
          rw[← inv_inv p, gt_iff_lt, one_lt_inv_iff₀] at hpgt
          field_simp at hpgt ⊢
          norm_cast
        have lhs_pos : A ^ (1 / p : ℝ) * B ^ (1 / q : ℝ) > 0 := by 
          exact mul_pos (Real.rpow_pos_of_pos h.1 (1 / p : ℝ)) (Real.rpow_pos_of_pos h.2 (1 / q : ℝ))
        have rhs_pos : A / p + B / q > 0 := by 
          exact add_pos (div_pos h.1 (by norm_cast; exact h2.1)) (div_pos h.2 (by norm_cast; exact h2.2))
        --rewrite the Young-type inequality using e ^ log (-) < e ^ log (-) and than argue using strict concavity of log, i.e. the strict Jensen's inequality
        rw[← Real.exp_log lhs_pos, ← Real.exp_log rhs_pos]
        rw[Real.exp_lt_exp, Real.log_mul (by have := Real.rpow_pos_of_pos h.1 (1 / p : ℝ); linarith) (by have := Real.rpow_pos_of_pos h.2 (1 / q : ℝ); linarith)]
        rw[Real.log_rpow h.1 (1 / p : ℝ), Real.log_rpow h.2 (1 / q : ℝ)]
        have strict_concave_log := strictConcaveOn_log_Ioi
        let w : Bool → ℝ := fun i => if i = 0 then (1 / p : ℝ) else (1 / q : ℝ)
        let f : Bool → ℝ := fun i => if i = 0 then A else B
        have h₀ : ∀ i ∈ ({0,1} : Finset Bool), 0 < w i := by 
          intro i hi
          simp at hi
          obtain h0|h1 := hi
          · rw[h0]
            simp[w]
            exact h2.1
          · rw[h1]
            simp[w]
            exact h2.2
        have hmem : ∀ i ∈ ({0,1} : Finset Bool), f i ∈ Set.Ioi 0 := by 
          intro i hi
          simp at hi
          obtain h0|h1 := hi
          · rw[h0]
            simp[f]
            exact h.1
          · rw[h1]
            simp[f]
            exact h.2
        --log is strictly concave on (0, +∞) and we can apply the strict Jensen's inequality
        have strict_jensen := StrictConcaveOn.lt_map_sum strict_concave_log h₀ (by simp[w]; rw[← one_div, ← one_div]; exact h1) hmem (by use 0; simp[f]; exact hAnB)
        have zero_mem : (0 : Bool) ∈ ({0, 1} : Finset Bool) := by simp 
        have one_mem : (1 : Bool) ∈ ({0, 1} : Finset Bool) := by simp
        simp[w, f] at strict_jensen 
        --after algebraic manipulation we obtain the desired inequality
        rw[← one_div, ← one_div] at strict_jensen
        nth_rw 2 [← mul_one A, ← mul_one B]
        rw[mul_div_assoc, mul_div_assoc]
        rw[mul_comm A, mul_comm B]
        exact strict_jensen 
      --if A ≠ B and p < 1 then A ^ (1 / p) * B ^ (1 / q) > A / p + B / q
      · intro hplt
        let s := A/B - 1
        let a := 1 / (p : ℝ)
        have den_bound : s ≥ -1 := by 
          have : A/B > 0 := by exact div_pos h.1 h.2
          simp[s]
          linarith
        have s_ne_zero : s ≠ 0 := by 
          simp[s]
          push_neg
          rw[sub_ne_zero]
          apply div_ne_one_of_ne
          exact hAnB
        have exp_bound : a > 1 := by 
          simp[a]
          field_simp
          rw[lt_one_div (by linarith) (by norm_cast; exact h2.1)]
          norm_num
          norm_cast
        --this is true by strict Bernoulli's inequality above, multiplying both sides by B
        have bernoulli := strict_bernoulli_inequality_mul_right den_bound s_ne_zero exp_bound h.2
        --the lhs becomes A ^ (1 / p) * B ^ (1 / q) after algebraic manipulation
        have lhs : A ^ (1 / p : ℝ) * B ^ (1 / q : ℝ) = B * (1 + s) ^ a := by 
          simp only [s, a]
          norm_num
          rw[Real.div_rpow (le_of_lt h.1) (le_of_lt h.2)]
          rw[← mul_div_assoc, mul_comm B, mul_div_assoc]
          nth_rw 2 [← Real.rpow_one B]
          rw[← Real.rpow_sub h.2]
          field_simp
          left
          rw[sub_div, div_self (by norm_cast)]
          rw[← rw_conj_exp]
        --the rhs becomes A / p + B / q after algebraic manipulation
        have rhs : A / p + B / q = B * (1 + a * s) := by 
          simp only [s, a]
          rw[mul_sub, mul_add, mul_sub]
          rw[← mul_assoc]
          nth_rw 2 [mul_comm B]
          rw[mul_assoc, ← mul_div_assoc, mul_comm B A, mul_div_assoc, div_self (by linarith)]
          rw[add_sub, add_comm (B * 1), ← add_sub]
          rw[← mul_sub B 1 (1 / (p : ℝ) * 1)]
          rw[mul_one, mul_one, ← rw_conj_exp]
          ring_nf
        --this yields the desired inequality
        rw[← lhs, ← rhs] at bernoulli
        exact bernoulli