import Mathlib

/- The real-valued function $f$ is defined for $0 \leq x \leq 1, f(0)=0, f(1)=1$, and
$ \frac{1}{2} \leq \frac{f(z)-f(y)}{f(y)-f(x)} \leq 2$
for all $0 \leq x < y < z \leq 1$ with $z - y = y - x$. Prove that
$\frac{1}{7} \leq f\left(\frac{1}{3}\right) \leq \frac{4}{7}$ -/
theorem inequalities_607971
  (f : ℝ → ℝ)
  (h₀ : f 0 = 0)
  (h₁ : f 1 = 1)
  (h₂ : ∀ x y z, 0 ≤ x → x < y → y < z → z ≤ 1 → (z - y) = (y - x) →
    1 / 2 ≤ (f z - f y) / (f y - f x) ∧ (f z - f y) / (f y - f x) ≤ 2) :
  1 / 7 ≤ f (1 / 3) ∧ f (1 / 3) ≤ 4 / 7 := by
    -- We set $f\left(\frac{1}{3}\right)=a$ and $f\left(\frac{2}{3}\right)=b$.
    let a := f (1/3)
    let b := f (2/3)
    -- Applying the inequality of the problem for $x=\frac{1}{3}, y=\frac{2}{3}$ and $z=1$,
    -- as well as for $x=0, y=\frac{1}{3}$, and $z=\frac{2}{3}$,
    -- we obtain $\frac{1}{2} \leq \frac{1-b}{b-a} \leq 2, \quad \frac{1}{2} \leq \frac{b-a}{a} \leq 2 $
    have h2_1 := h₂ (1/3) (2/3) 1 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    have h2_2 := h₂ 0 (1/3) (2/3) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    rw [show f (1/3) = a by rfl]
    rw [show f (1/3) = a by rfl, show f (2/3) = b by rfl, h₁] at h2_1
    rw [show f (1/3) = a by rfl, show f (2/3) = b by rfl,
        h₀, show a - 0 = a by simp] at h2_2
    -- If $a < 1$. A similar contradiction would be implied by the assumption $b-a≤0$ and $b-a>0$
    have ha_lt_one : a < 1 := by
      by_contra ha_ge_one
      have hb_sub_a_pos: b - a > 0 := by
        apply (div_pos_iff_of_pos_right (by linarith)).mp (by linarith [h2_2.1])
      have h1_sub_b_pos: 1 - b > 0 := by
        apply (div_pos_iff_of_pos_right hb_sub_a_pos).mp (by linarith [h2_1.1])
      have : ¬ (1 - b > 0) := not_lt_of_gt (by linarith)
      contradiction
    have hb_sub_a_pos: b - a > 0 := by
      by_contra hb_sub_a_neg
      simp at hb_sub_a_neg
      cases eq_or_lt_of_le hb_sub_a_neg with
      | inl h_eq =>
        rw [h_eq] at h2_1
        simp at h2_1
        have this: ¬ ((2:ℝ) ≤ (0:ℝ)) := by norm_num
        exact this h2_1
      | inr h_lt =>
        have htmp: (b - 1) / (a - b) > 0 := by
          calc
            _ = -(1 - b) / -(b - a) := by simp
            _ = (1 - b) / (b - a)   := by rw [neg_div_neg_eq]
          linarith [h2_1.1]
        have hb_sub_1_pos := (div_pos_iff_of_pos_right (by linarith)).mp htmp
        linarith
    have ha_pos: a > 0 := (div_pos_iff_of_pos_left hb_sub_a_pos).mp (by linarith [h2_2.1])
    -- so, we have $a \leq 2 b-2 a, b-a \leq 2 a, b-a \leq 2-2 b$, and $1-b \leq 2 b-2 a$
    have hi1: a ≤ b * 2 - a * 2 := by
      have := (div_le_div_iff₀ (by linarith) ha_pos).mp h2_2.1
      ring_nf at this
      rw [show -(a * 2) + b * 2 = b * 2 - (a * 2) by ring] at this
      exact this
    have hi2: b - a ≤ a * 2 := by
      have := (mul_inv_le_iff₀ ha_pos).mp h2_2.2
      ring_nf at this
      exact this
    have hi3: b - a ≤ 2 - b * 2 := by
      have := (div_le_div_iff₀ (by linarith) hb_sub_a_pos).mp h2_1.1
      ring_nf at this
      exact this
    have hi4: 1 - b ≤ b * 2 - a * 2 := by
      have := (mul_inv_le_iff₀ hb_sub_a_pos).mp h2_1.2
      ring_nf at this
      exact this
    -- Of these inequalities the first and third imply $3 a \leq 2 b$ and $3 b \leq 2+a$.
    have hi5: a * 3 ≤ b * 2 := by linarith
    have hi6: b * 3 ≤ 2 + a := by linarith
    -- Eliminate $b$ to obtain $3 a \leq \frac{4}{3}+\frac{2 a}{3}$, $a \leq \frac{4}{7}$.
    have hi7: a * 3 ≤ (4 / 3) + (2 / 3) * a := by linarith
    have hi8: a ≤ (4 / 7) := by linarith
    -- In a corresponding manner, the second and fourth inequality imply $1+2 a \leq 3 b$ and $b \leq 3 a$,
    have hi9: 1 + a * 2 ≤ b * 3 := by linarith
    have hi10: b ≤ a * 3 := by linarith
    -- from which $1 \leq 7 a$ or $\frac{1}{7} \leq a$ follows.
    have hi11: 1 ≤ a * 7 := by linarith
    have hi12: 1 / 7 ≤ a := by linarith
    exact ⟨hi12, hi8⟩
