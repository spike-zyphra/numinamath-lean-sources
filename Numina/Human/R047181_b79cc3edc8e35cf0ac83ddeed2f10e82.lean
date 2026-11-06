import Mathlib

open Real
open scoped BigOperators

/- Let $a, b, c$ be the sides of a triangle, with $a+b+c=1$, and let $n \geq 2$ be an integer. Show that

$$
\sqrt[n]{a^{n}+b^{n}}+\sqrt[n]{b^{n}+c^{n}}+\sqrt[n]{c^{n}+a^{n}}<1+\frac{\sqrt[n]{2}}{2}
$$ -/
theorem inequalities_607122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : a + b > c) (h₂ : a + c > b) (h₃ : b + c > a) (hsum : a + b + c = 1)
    (n : ℕ) (hn : 2 ≤ n) :
    (a ^ n + b ^ n) ^ ((1 : ℝ) / n) +
    (b ^ n + c ^ n) ^ ((1 : ℝ) / n) +
    (c ^ n + a ^ n) ^ ((1 : ℝ) / n) <
    1 + 2 ^ ((1 : ℝ) / n) / 2 := by
  -- Without loss of generality, assume $a \leq b \leq c$. As $a+b&gt;c$, we have
  wlog ho : a ≤ b ∧ b ≤ c generalizing a b c with H
  · simp at ho
    by_cases hle : a ≤ b
    · obtain ho := ho hle
      by_cases hac : a ≤ c
      · obtain H := H a c b ha hc hb h₂ h₁ (by rw [add_comm]; exact h₃) (by rw [←hsum]; ring) ⟨hac, le_of_lt ho⟩
        apply lt_of_eq_of_lt ?_ H
        ring_nf
      · simp at hac
        obtain H := H c a b hc ha hb (by rw [add_comm]; exact h₂) (by rw [add_comm]; exact h₃) h₁ (by rw [←hsum]; ring) ⟨le_of_lt hac, hle⟩
        apply lt_of_eq_of_lt ?_ H
        ring_nf
    · simp at hle
      by_cases hbc : b ≤ c
      · by_cases hac : a ≤ c
        · obtain H := H b a c hb ha hc (by rw [add_comm]; exact h₁) h₃ h₂ (by rw [←hsum]; ring) ⟨le_of_lt hle, hac⟩
          apply lt_of_eq_of_lt ?_ H
          ring_nf
        · simp at hac
          obtain H := H b c a hb hc ha h₃ (by rw [add_comm]; exact h₁) (by rw [add_comm]; exact h₂) (by rw [←hsum]; ring) ⟨hbc, le_of_lt hac⟩
          apply lt_of_eq_of_lt ?_ H
          ring_nf
      · simp at hbc
        obtain H := H c b a hc hb ha (by rw [add_comm]; exact h₃) (by rw [add_comm]; exact h₂) (by rw [add_comm]; exact h₁) (by rw [←hsum]; ring) ⟨le_of_lt hbc, le_of_lt hle⟩
        apply lt_of_eq_of_lt ?_ H
        ring_nf
  · -- $$ \frac{\sqrt[n]{2}}{2}=\frac{\sqrt[n]{2}}{2}(a+b+c)&gt;
    -- \frac{\sqrt[n]{2}}{2}(c+c)=\sqrt[n]{2 c^{n}} \geq \sqrt[n]{b^{n}+c^{n}} \quad \quad[2 \text { marks }] $$
    have h₁ : (2 : ℝ) ^ (1 / n : ℝ) / 2 > (b ^ n + c ^ n) ^ ((1 : ℝ) / n) := by
      calc
        (2 : ℝ) ^ (1 / n : ℝ) / 2 = (2 : ℝ) ^ (1 / n : ℝ) / 2 * (a + b + c) := by
          rw [hsum]
          ring
        _ > (2 : ℝ) ^ (1 / n : ℝ) / 2 * (c + c) := by rel [h₁]
        _ = (2 : ℝ) ^ (1 / n : ℝ) * c := by field_simp; ring
        _ = (2 * c ^ (n : ℝ)) ^ (1 / n : ℝ) := by
          rw [mul_rpow, ←rpow_mul]
          · congr
            rw [mul_div_cancel₀]
            · simp
            · simp
              exact Nat.not_eq_zero_of_lt hn
          · exact le_of_lt hc
          · simp
          · apply rpow_nonneg
            exact le_of_lt hc
        _ ≥ (b ^ n + c ^ n) ^ ((1 : ℝ) / n : ℝ) := by
          apply rpow_le_rpow
          · apply add_nonneg
            · apply pow_nonneg
              exact le_of_lt hb
            · apply pow_nonneg
              exact le_of_lt hc
          · apply sub_nonneg.mp
            norm_cast
            ring_nf
            simp
            apply pow_le_pow_left₀
            · exact le_of_lt hb
            · exact ho.2
          · simp
    -- As $a \leq c$ and $n \geq 2$, we have1
    -- $$ \begin{aligned} \left(c^{n}+a^{n}\right)-\left(c+\frac{a}{2}\right)^{n}
    -- & =a^{n}-\sum_{k=1}^{n}\binom{n}{k} c^{n-k}\left(\frac{a}{2}\right)^{k} \
    -- & \leq\left[1-\sum_{k=1}^{n}\binom{n}{k}\left(\frac{1}{2}\right)^{k}\right] a^{n} \quad\left(\text { since } c^{n-k}
    -- \geq a^{n-k}\right) \ & =\left[\left(1-\frac{n}{2}\right)-\sum_{k=2}^{n}\binom{n}{k}\left(\frac{1}{2}\right)^{k}\right] a^{n}
    -- &lt;0 \end{aligned} $$
    let f (y x : ℝ) := (x + y / 2) ^ (n : ℝ) - x ^ (n : ℝ)
    have hf {y : ℝ} (hy : y > 0) : MonotoneOn (f y) (Set.Ioi 0) := by
      refine monotoneOn_of_deriv_nonneg ?hD ?hf ?hf' ?hf'_nonneg
      · exact convex_Ioi 0
      · simp [f]
        apply ContinuousOn.sub
        · apply ContinuousOn.pow
          apply ContinuousOn.add
          · exact continuousOn_id' (Set.Ioi 0)
          · exact continuousOn_const
        · apply ContinuousOn.pow
          apply continuousOn_id'
      · simp [f]
        apply DifferentiableOn.sub
        · apply DifferentiableOn.pow
          apply DifferentiableOn.add
          · exact differentiableOn_id'
          · exact differentiableOn_const (y / 2)
        · apply DifferentiableOn.pow
          apply differentiableOn_id'
      · intro x hx
        simp [f]
        simp at hx
        apply mul_le_mul_of_nonneg_left
        · apply pow_le_pow_left₀
          · exact le_of_lt hx
          · simp
            apply div_nonneg
            · exact le_of_lt hy
            · simp
        · simp
    have h {a b : ℝ} (ha : a > 0) (hb : b > 0) (hab : a ≤ b) : a ^ (n : ℝ) < (b + a / 2) ^ (n : ℝ) - b ^ (n : ℝ) := by
      calc
        a ^ (n : ℝ) < ((3 / 2 : ℝ) ^ (n : ℝ) - 1) * a ^ (n : ℝ) := by
          apply lt_of_eq_of_lt  (b := 1 * a ^ (n : ℝ))
          · simp
          · apply mul_lt_mul_of_pos_right
            · apply lt_sub_left_of_add_lt
              norm_num
              apply lt_of_lt_of_le (b := (3 / 2 : ℝ) ^ 2)
              · ring_nf
                norm_num
              · apply pow_le_pow_right₀
                · norm_num
                · exact hn
            · apply rpow_pos_of_pos
              exact ha
        _ = f a a := by
          simp [f]
          ring
        _ ≤ f a b := by
          exact hf ha (by simp [ha]) (by simp [hb]) hab
        _ = _ := by simp [f]
    -- Thus
    -- $$ \sqrt[n]{c^{n}+a^{n}}&lt;c+\frac{a}{2} . \quad[3 \text { marks }] $$
    have h {a b : ℝ} (ha : a > 0) (hb : b > 0) (hab : a ≤ b) :  (a ^ (n : ℝ) + b ^ (n : ℝ)) ^ (1 / n : ℝ) < b + a / 2 := by
      apply rpow_lt_rpow_iff ?_ ?_ (show n > (0 : ℝ) by simp; exact Nat.zero_lt_of_lt hn) |>.mp
      · rw [←rpow_mul, div_mul_cancel₀, rpow_one]
        · apply h ha hb at hab
          simp at hab
          simp
          exact lt_tsub_iff_right.mp hab
        · simp
          exact Nat.not_eq_zero_of_lt hn
        · simp
          apply add_nonneg
          · apply pow_nonneg
            exact le_of_lt ha
          · apply pow_nonneg
            exact le_of_lt hb
      · simp
        apply rpow_nonneg
        apply add_nonneg
        · apply pow_nonneg
          exact le_of_lt ha
        · apply pow_nonneg
          exact le_of_lt hb
      · linarith
    have h₂ : (a ^ (n : ℝ) + b ^ (n : ℝ)) ^ (1 / n : ℝ) < b + a / 2 := h ha hb ho.1
    -- Likewise
    -- $$ \sqrt[n]{b^{n}+a^{n}}&lt;b+\frac{a}{2} \quad \quad[1 \text { mark }] $$
    have h₃ : (a ^ (n : ℝ) + c ^ (n : ℝ)) ^ (1 / n : ℝ) < c + a / 2 := h ha hc (le_trans ho.1 ho.2)
    -- Adding (1), (2) and (3), we get
    -- $$ \sqrt[n]{a^{n}+b^{n}}+\sqrt[n]{b^{n}+c^{n}}+\sqrt[n]{c^{n}+a^{n}}&lt;\frac{\sqrt[n]{2}}{2}+c+\frac{a}{2}+b+\frac{a}{2}=1+\frac{\sqrt[n]{2}}{2} . \quad[1 \text { mark }] $$
    calc
      _ < b + a / 2 + 2 ^ (1 / n : ℝ) / 2 + (c + a / 2) := by
        simp at h₂ h₃
        rw [add_comm] at h₃
        simp at h₁ ⊢
        rel [h₁, h₂, h₃]
      _ = _ := by
        rw [←hsum]
        ring
