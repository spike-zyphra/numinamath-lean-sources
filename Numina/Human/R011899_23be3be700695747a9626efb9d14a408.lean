import Mathlib
/-
Given $x, y$ are positive numbers satisfying $x+y=1$, and $n$ is an integer no less than 2. Prove:
$$
\frac{x^{n}}{x+y^{3}}+\frac{y^{n}}{x^{3}+y} \geqslant \frac{2^{4-n}}{5} .
$$
-/
theorem inequalites_312031 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (4 - n : ℤ) / 5 ≤ x ^ n / (x + y ^ 3) + y ^ n / (x ^ 3 + y) := by
-- Proof: Since the function $z=t^{m}$ (where $m$ is a constant greater than 0) is an increasing function on $(0,+\infty)$,
-- we have $$ \begin{array}{l} (x-y)\left(x^{n+3}-y^{n+3}\right) \geqslant 0, \ (x-y)\left(x^{n-1}-y^{n-1}\right) \geqslant 0 . \end{array} $$
have h₁ {n : ℕ} : (x -y) * (x ^ (n + 3) - y ^ (n + 3)) ≥ 0 := by
  by_cases hxy : x < y
  · apply mul_nonneg_of_nonpos_of_nonpos
    · apply le_of_lt
      apply sub_neg_of_lt hxy
    · simp
      apply pow_le_pow_left₀ ?_ (le_of_lt hxy)
      positivity
  · push_neg at hxy
    apply mul_nonneg
    · apply sub_nonneg_of_le hxy
    · apply sub_nonneg_of_le
      apply pow_le_pow_left₀ ?_ hxy
      positivity
have h₂ {n : ℕ} (hn : n ≥ 1) : (x - y) * (x ^ n * y - y ^ n * x) ≥ 0 := by
  by_cases hxy : x < y
  · apply mul_nonneg_of_nonpos_of_nonpos
    · apply le_of_lt
      apply sub_neg_of_lt hxy
    · simp
      suffices h : x ^ (n - 1) ≤ y ^ (n - 1)
      · apply mul_le_mul_of_nonneg_left (a := x * y) at h
        obtain h := h (by positivity)
        apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
        · nth_rw 1 [show n = n - 1 + 1 by rw [Nat.sub_add_cancel hn]]
          ring
        · nth_rw 2 [show n = n - 1 + 1 by rw [Nat.sub_add_cancel hn]]
          ring
      · apply pow_le_pow_left₀ ?_ (le_of_lt hxy)
        positivity
  · push_neg at hxy
    apply mul_nonneg
    · apply sub_nonneg_of_le hxy
    · apply sub_nonneg_of_le
      suffices h : y ^ (n - 1) ≤ x ^ (n - 1)
      · apply mul_le_mul_of_nonneg_left (a := x * y) at h
        obtain h := h (by positivity)
        apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
        · nth_rw 1 [show n = n - 1 + 1 by rw [Nat.sub_add_cancel hn]]
          ring
        · nth_rw 2 [show n = n - 1 + 1 by rw [Nat.sub_add_cancel hn]]
          ring
      · apply pow_le_pow_left₀ ?_ hxy
        positivity
-- Therefore, $$ 2\left(\frac{x^{n+1}}{x+y^{3}}+\frac{y^{n+1}}{x^{3}+y}\right)-\left(\frac{x^{n}}{x+y^{3}}+\frac{y^{n}}{x^{3}+y}\right) $$ $$ \begin{aligned} = & \frac{2 x^{n+1}-x^{n}(x+y)}{x+y^{3}}+\frac{2 y^{n+1}-y^{n}(x+y)}{x^{3}+y} \ = & \frac{x^{n}(x-y)}{x+y^{3}}+\frac{y^{n}(y-x)}{x^{3}+y} \ = & \frac{x-y}{\left(x+y^{3}\right)\left(x^{3}+y\right)}\left[x^{n}\left(x^{3}+y\right)-y^{n}\left(x+y^{3}\right)\right] \ = & \frac{1}{\left(x+y^{3}\right)\left(x^{3}+y\right)}\left[(x-y)\left(x^{n+3}-y^{n+3}\right)+\right. \ & \left.x y(x-y)\left(x^{n-1}-y^{n-1}\right)\right] \end{aligned} $$ $$ \geqslant 0 \text {. } $$
have hsub_nonneg {n : ℕ} (hn : n ≥ 1) : 2 * (x ^ (n + 1) / (x + y ^ 3) + y ^ (n + 1) / (x ^ 3 + y)) - (x ^ n / (x + y ^ 3) + y ^ n / (x ^ 3 + y)) ≥ 0 := by
  field_simp
  rw [show x ^ n = x ^ n * (x + y) by rw [hxy]; ring]
  rw [show y ^ n = y ^ n * (x + y) by rw [hxy]; ring]
  apply div_nonneg
  · trans (x - y) * (x ^ (n + 3) - y ^ (n + 3)) + (x - y) * (x ^ n * y - y ^ n * x)
    · apply add_nonneg
      · apply h₁
      · apply h₂ hn
    · apply le_of_eq
      ring
  · positivity
-- Thus, $\frac{x^{n+1}}{x+y^{3}}+\frac{y^{n+1}}{x^{3}+y} \geqslant \frac{1}{2}\left(\frac{x^{n}}{x+y^{3}}+\frac{y^{n}}{x^{3}+y}\right)$ $$ \begin{array}{l} \geqslant \frac{1}{2^{2}}\left(\frac{x^{n-1}}{x+y^{3}}+\frac{y^{n-1}}{x^{3}+y}\right) \geqslant \cdots \ \geqslant \frac{1}{2^{n-1}}\left(\frac{x^{2}}{x+y^{3}}+\frac{y^{2}}{x^{3}+y}\right) . \end{array} $
-- Therefore, $\frac{x^{n}}{x+y^{3}}+\frac{y^{n}}{x^{3}+y} \geqslant 2^{2-n}\left(\frac{x^{2}}{x+y^{3}}+\frac{y^{2}}{x^{3}+y}\right)$.
have hinduct : x ^ n / (x + y ^ 3) + y ^ n / (x ^ 3 + y) ≥ 2 ^ (2 - n : ℤ) * (x ^ 2 / (x + y ^ 3) + y ^ 2 / (x ^ 3 + y)) := by
  induction n, hn using Nat.le_induction
  · norm_num
  · rename_i n hn ih
    trans 1 / 2 * (x ^ n / (x + y ^ 3) + y ^ n / (x ^ 3 + y))
    · linarith only [hsub_nonneg (by exact Nat.one_le_of_lt hn)]
    trans 1 / 2 * (2 ^ (2 - n : ℤ) * (x ^ 2 / (x + y ^ 3) + y ^ 2 / (x ^ 3 + y)))
    · rel [ih]
    · apply le_of_eq
      rw [←mul_assoc]
      congr
      rw [Nat.cast_add, show 1 / 2 = (2 : ℝ) ^ (-1 : ℤ) by norm_num]
      rw [←zpow_add₀]
      · congr; ring
      · simp
apply le_trans ?_ hinduct
suffices h : x ^ 2 / (x + y ^ 3) + y ^ 2 / (x ^ 3 + y) ≥ 4 / 5
· trans 2 ^ (2 - n : ℤ) * (4 / 5)
  · apply le_of_eq
    field_simp
    rw [show  (4 : ℝ)= 2 ^ (2 : ℤ) by norm_num, ←zpow_add₀]
    · congr; ring
    · simp
  · rel [h]
· field_simp
  apply div_le_div_iff₀ (by positivity) (by positivity) |>.mpr
  -- Let $t=x y$, then $t \leqslant\left(\frac{x+y}{2}\right)^{2}=\frac{1}{4}$, and $x^{4}+y^{4}=$ $1-4 t+2 t^{2}, x^{5}+y^{5}=1-5 t+5 t^{2}$.
  let t := x * y
  have ht : t ≤ 1 / 4 := by
    trans (x + y) ^ 2 / 4
    · unfold t
      apply sub_nonneg.mp
      trans (x / 2 - y / 2) ^ 2
      · positivity
      · apply le_of_eq
        ring
    · simp [hxy]
  have h₁ : x ^ 4 + y ^ 4 = 1 - 4 * t + 2 * t ^ 2 := by
    rw [show x ^ 4 + y ^ 4 = (x + y) ^ 4 - 4 * (x + y) ^ 2 * x * y + 2 * (x * y) ^ 2 by ring]
    rw [hxy]
    ring
  have h₂ : x ^ 5 + y ^ 5 = 1 - 5 * t + 5 * t ^ 2 := by
    rw [show x ^ 5 + y ^ 5 = (x + y) * (x ^ 4 + y ^ 4 - x * y * ((x + y) ^ 2 - 2 * x * y) + x ^ 2 * y ^ 2) by ring]
    rw [hxy, h₁]
    ring
  suffices h : 5 * (x ^ 5 + y ^ 5 + t) ≥ 4 * (x ^ 4 + y ^ 4 + t + t ^ 3)
  · apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
    · unfold t
      ring
    · unfold t
      rw [show x * y = x * y * (x + y) by rw [hxy]; ring]
      ring
  · -- Thus, $$ \begin{array}{l} \frac{x^{2}}{x+y^{3}}+\frac{y^{2}}{x^{3}+y} \geqslant \frac{4}{5} \ \Leftrightarrow 5\left[x^{2}\left(x^{3}+y\right)+y^{2}\left(x+y^{3}\right)\right] \ \quad \geqslant 4\left(x+y^{3}\right)\left(x^{3}+y\right) \ \Leftrightarrow 5\left(x^{5}+y^{5}+t\right) \geqslant 4\left(x^{4}+y^{4}+t+t^{3}\right) \ \Leftrightarrow 5\left(1-4 t+5 t^{2}\right) \geqslant 4\left(1-3 t+2 t^{2}+t^{2}\right) \ \Leftrightarrow 4 t^{3}-17 t^{2}+8 t-1 \leqslant 0 \ \Leftrightarrow(4 t-1)\left(t^{2}-4 t+1\right) \leqslant 0 \ \Leftrightarrow(1-4 t)\left[t^{2}+(1-4 t)\right] \geqslant 0 . \end{array} $$
    rw [h₁, h₂]
    have h : 4 * t ^ 3 - 17 * t ^ 2 + 8 * t - 1 ≤ 0 := by
      -- Since $1-4 t \geqslant 0$, the last inequality holds, thus, $\frac{x^{2}}{x+y^{3}}+\frac{y^{2}}{x^{3}+y} \geqslant \frac{4}{5}$.
      -- In summary, the original inequality holds. (Song Qing, Nanchang University Affiliated High School, 330029)
      trans (4 * t - 1) * (t ^ 2 + (1 - 4 * t))
      · apply le_of_eq
        ring
      · apply mul_nonpos_of_nonpos_of_nonneg
        · linarith only [ht]
        · apply add_nonneg
          · positivity
          · linarith only [ht]
    linarith only [h]
