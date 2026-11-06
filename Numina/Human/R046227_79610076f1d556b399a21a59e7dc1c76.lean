import Mathlib

/-- Auxiliary lemma :  Quadratic Formula when discriminant is nonegative. -/
lemma Real.quadratic_eq_zero_iff {a b c : ℝ} (ha : a ≠ 0) (h : 0 ≤ discrim a b c) (x : ℝ) :
    a * x ^ 2 + b * x + c = 0 ↔
    x = (-b + sqrt (discrim a b c)) / (2 * a) ∨
    x = (-b - sqrt (discrim a b c)) / (2 * a) := by
  let d := sqrt <| discrim a b c
  have : discrim a b c = d * d := Eq.symm <| mul_self_sqrt h
  rw [pow_two, _root_.quadratic_eq_zero_iff ha this x]

/-- The line $y = 3$ intersects the graph of $y = 4x^2 + x - 1$ at the points $A$ and $B$. The distance between $A$ and $B$ can be written as $\frac{\sqrt{m}}{n}$, where $m$ and $n$ are positive integers that do not share any factors other than one. Find the value of $m - n$.-/
theorem algebra_4081 (m n : ℕ)
  (hmn_pos : m > 0 ∧ n > 0)
  (x₁ x₂ : ℝ)
  (h_eq₁ : 4 * x₁^2 + x₁ - 1 = 3)
  (h_eq₂ : 4 * x₂^2 + x₂ - 1 = 3)
  (WLOG: x₁ > x₂)
  (h_distance : abs (x₁ - x₂) = Real.sqrt m / n)
  (h_coprime : Nat.Coprime m n) : m - n = 61 := by
-- the discriminant of quadratic $4x^2+x-4=0$.
have h1: discrim (4:ℝ) (1:ℝ) (-4:ℝ) = 65:= by simp [discrim];ring
have h0: (4:ℝ) ≠ 0 := by norm_num
have h2:= Real.quadratic_eq_zero_iff h0 (by linarith) x₁
have h3:= h2.mp (by linarith)
have h4:= Real.quadratic_eq_zero_iff h0 (by linarith) x₂
have h5:= h4.mp (by linarith)
cases h3
cases h5
linarith
rename_i hx hy
rw [hx,hy,h1] at h_distance
-- After simplifing, we get the distance between A and B is $\sqrt {65} / 4$.
field_simp at h_distance
ring_nf at h_distance
have h6: √65 * (1 / 4) >= 0 := by positivity
have h7: |√65 * (1 / 4)| = √65 * (1 / 4) := by simp
rw [h7] at h_distance
field_simp at h_distance
have h8:= h_distance
rw [← pow_left_inj (by positivity) (by positivity) (by norm_num : 2 ≠ 0)] at h8
-- square both sides at $\sqrt {65} = \frac {\sqrt m * 4}  n$
norm_num [mul_pow, pow_two] at h8
by_cases n0 : n = 0
· simp [n0] at h8
ring_nf at h8
field_simp at h8
norm_cast at h8
obtain ⟨m, rfl⟩ : 65 ∣ m := by omega
obtain ⟨n, rfl⟩ : 4 ∣ n := by rw [← Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]; omega
norm_num [mul_pow, ← mul_assoc, mul_right_comm _ _ 16] at h8
subst h8
-- Here we have $n=1$ because of m and n are coprime.
simp [pow_two, Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right] at h_coprime
norm_num [h_coprime.2.2]

cases h5
rename_i hx hy
rw [hx,hy] at WLOG
rw [h1] at WLOG
ring_nf at WLOG
apply False.elim
simp at WLOG
linarith
linarith
