import Mathlib

/-Let $k$ be a real number such that $k > 1$ and
\[\sum_{n=1}^{\infty} \frac{5n-1}{k^n} = \frac{13}{4}.\]Find $k.$-/
theorem algebra_14900 {k : ℝ} (hk : k > 1) (h : ∑' n : ℕ, (5 * n + 4) / k ^ (n + 1) = 13 / 4):
    k = 3 := by 
  set S := ∑' n : ℕ, (5 * n + 4) / k ^ (n + 1) with hS -- Suppose the sum of (5 * n + 4) / k ^ (n + 1) is S
  -- prove (5 * n + 4) / k ^ (n + 1) * k = (5 * n + 4) / k ^ n
  have eq1(n : ℕ) : (5 * n + 4) / k ^ (n + 1) * k = (5 * n + 4) / k ^ n := by
      field_simp
      rw [mul_assoc]
      rw [<-pow_succ']
  -- calculate S * k directly by eq1
  have eq_mul_k : ∑' n : ℕ, (5 * n + 4) / k ^ n = S * k := by
    calc
      ∑' n : ℕ, (5 * n + 4) / k ^ n = ∑' n : ℕ, (5 * n + 4) / k ^ (n + 1) * k := by simp_rw[eq1]
      _ = (∑' n : ℕ, (5 * n + 4) / k ^ (n + 1)) * k := by rw [tsum_mul_right]
      _ = S * k := by rw [<-hS]
  -- have a lemma that Summable f when ∑'n : ℕ, f n > 0
  have ne_zero_summable (f : ℕ → ℝ) : ∑' n : ℕ, f n > 0 → Summable f := by
    contrapose
    intro hsum
    apply tsum_eq_zero_of_not_summable at hsum
    intro s
    linarith only [s, hsum]
  -- prove (5 * n + 4) / k ^ n summable
  have summable₁ : Summable fun (n : ℕ) => (5 * n + 4) / k ^ n := by
    have pos_sum : ∑' n : ℕ, (5 * n + 4) / k ^ n > 0 := by
      calc
        ∑' n : ℕ, (5 * n + 4) / k ^ n = S * k := by rw [eq_mul_k]
        _ = 13 / 4 * k := by rw [h]
        _ > 0 := by positivity
    apply ne_zero_summable at pos_sum
    exact pos_sum
  -- prove (5 * (n + 1) + 4) / k ^ (n + 1) summable
  have summable₂ : Summable fun (n : ℕ) => (5 * (n + 1) + 4) / k ^ (n + 1) := by
    rw [<-summable_nat_add_iff 1] at summable₁
    norm_cast at summable₁ ⊢
  -- prove (5 * n + 4) / k ^ (n + 1) summable
  have summable₃ : Summable fun (n : ℕ) => (5 * n + 4) / k ^ (n + 1) := by
    have pos_num : ∑' n : ℕ, (5 * n + 4) / k ^ (n + 1) > 0 := by rw [<-hS, h]; positivity
    apply ne_zero_summable at pos_num
    exact pos_num
  -- Dislocation subtraction so that we can simplify the expression of S
  have eq_sub : S * (k - 1) = 4 + ∑' n : ℕ, 5 / k ^ (n + 1) := by -- simplify to geometric series
    calc
      S * (k - 1) = S * k - S := by ring_nf
      _ = ∑' n : ℕ, (5 * n + 4) / k ^ n - S := by rw [<-eq_mul_k]
      _ = 4 + ∑' n : ℕ, (5 * (n + 1) + 4) / k ^ (n + 1) - S := by rw [tsum_eq_zero_add]; simp; exact summable₁
      _ = 4 + (∑' n : ℕ, (5 * (n + 1) + 4) / k ^ (n + 1) - ∑' n : ℕ, (5 * n + 4) / k ^ (n + 1)) := by rw [hS]; rw [add_sub_assoc]
      _ = 4 + ∑' (n : ℕ), ((5 * (n + 1) + 4) / k ^ (n + 1) - (5 * n + 4) / k ^ (n + 1)) := by rw [<-@tsum_sub]; repeat assumption
      _ = 4 + ∑' (n : ℕ), 5 / k ^ (n + 1) := by field_simp; ring_nf; symm; ring_nf
  clear summable₁ summable₂ summable₃  
  -- calculate the sum of geometric series
  have h_geo₁ : HasSum (fun n => (1 / k) ^ n) (1 - (1 / k))⁻¹ := by
    apply hasSum_geometric_of_lt_one
    positivity
    -- prove 1 / k < 1 by k > 1
    rw [one_div_lt]
    field_simp
    linarith only [hk]
    repeat positivity
  -- depends on the expression above, we have HasSum (fun n => 5 / k ^ (n + 1)) (k * 5 / ((k - 1) * k))
  have h_geo₂ : HasSum (fun n => 5 / k ^ (n + 1)) (k * 5 / ((k - 1) * k)) := by
    -- exactly multiply the h_geo₁ by a constant 
    have hgeo : HasSum (fun n => ((1 / k) ^ n) * (1 / k) * 5) ((1 - (1 / k))⁻¹ * (1 / k) * 5) := by
      repeat apply HasSum.mul_right
      exact h_geo₁
    field_simp at hgeo
    simp_rw [<-pow_succ] at hgeo 
    exact hgeo
  clear h_geo₁
  -- finally we get a expression of S and k without tsum
  have eq : S * (k - 1) = 4 + k * 5 / ((k - 1) * k) := by
    calc
      S * (k - 1) = 4 + ∑' n : ℕ, 5 / k ^ (n + 1) := by rw [eq_sub]
      _ = 4 + k * 5 / ((k - 1) * k) := by apply HasSum.tsum_eq at h_geo₂; rw [h_geo₂]
  clear h_geo₂ eq_sub eq_mul_k eq1 hS
  -- substitute the S
  have eq₁ : 13 / 4 * (k - 1) = (4 * (k - 1) + 5) / (k - 1) := by
    rw [mul_comm k 5, mul_div_mul_right] at eq 
    rw [h] at eq
    rw [add_div'] at eq
    exact eq
    repeat linarith only [hk]
  -- prove 13 / 4 * (k - 1) ^ 2 = 4 * (k - 1) + 5
  have eq₂ : 13 / 4 * (k - 1) * (k - 1) = 4 * (k - 1) + 5 := by
    calc
      13 / 4 * (k - 1) * (k - 1) = (4 * (k - 1) + 5) / (k - 1) * (k - 1) := by rw [eq₁]
      _ = 4 * (k - 1) + 5 := by rw [div_mul_cancel₀]; linarith only [hk]
  clear eq₁
  -- simplify to 13k^2 - 26k + 13 = 16k + 4
  field_simp at eq₂
  ring_nf at eq₂
  -- simplify to (k - 3) * (13 * k - 3) = 0
  have eq₃ : (k - 3) * (13 * k - 3) = 0 := by
    ring_nf 
    linarith only [eq₂]
  clear eq₂
  -- so that we get k = 3 or k = 3 / 13
  rw [mul_eq_zero] at eq₃
  cases eq₃ with
  | inl hk1 =>
    linarith only [hk1]
  | inr hk1 =>
    linarith only [hk1, hk]
  