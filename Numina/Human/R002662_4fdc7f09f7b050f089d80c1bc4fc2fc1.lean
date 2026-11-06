import Mathlib

open Real Cubic Matrix

/-- Let $s_k$ denote the sum of the $\textit{k}$th powers of the roots of the polynomial
$x^3-5x^2+8x-13$. In particular, $s_0=3$, $s_1=5$, and $s_2=9$. Let $a$, $b$, and $c$ be real
numbers such that $s_{k+1} = a \, s_k + b \, s_{k-1} + c \, s_{k-2}$ for $k = 2$, $3$, $....$
What is $a+b+c$?

$\textbf{(A)} \; -6 \qquad \textbf{(B)} \; 0 \qquad \textbf{(C)} \; 6 \qquad \textbf{(D)} \; 10 \qquad \textbf{(E)} \; 26$ -/
theorem algebra_98422 {f : Cubic ℝ} (hf : f = Cubic.mk 1 (-5) 8 (-13))
    {p q r : ℝ} (hfr : f.roots = {p, q, r}) {s : ℕ → ℝ} (hs : ∀ k, s k = p^k + q^k + r^k)
    {a b c : ℝ} (habc : ∀ k, s (k + 3) = a * s (k + 2) + b * s (k + 1) + c * s k) :
    a + b + c = 10 := by

  -- We want to show that $a + b + c = 10$. It suffices to show that $a = 5$, $b = -8$, and $c = 13$.
  suffices a = 5 ∧ b = -8 ∧ c = 13 by linarith only [this]

  -- Let $p, q$, and $r$ be the roots of the polynomial. By Vieta's Formulae, we have
  -- $p + q + r = 5$, $pq + qr + rp = 8$, and $pqr = 13$.
  have pqr_sum : p + q + r = 5 := by
    suffices -5 = - (p + q + r) by linarith only [this]
    convert Cubic.b_eq_three_roots (φ := RingHom.id ℝ) (by simp [hf]) hfr using 1
    · simp [hf]
    · simp [hf]

  have pqr_two_sum : p * q + p * r + q * r = 8 := by
    suffices 8 = p * q + p * r + q * r by linarith only [this]
    convert Cubic.c_eq_three_roots (φ := RingHom.id ℝ) (by simp [hf]) hfr using 1
    · simp [hf]
    · simp [hf]

  have pqr_mul : p * q * r = 13 := by
    suffices -13 = -(p * q * r) by linarith only [this]
    convert Cubic.d_eq_three_roots (φ := RingHom.id ℝ) (by simp [hf]) hfr using 1
    · simp [hf]
    · simp [hf]

  -- We know $s_k = p^k + q^k + r^k$. Consider $(p+q+r)(s_k) =5s_k$.
  have h1 (k) :=
    calc 5 * s k = (p + q + r) * (p^k + q^k + r^k) := by rw [pqr_sum, hs]
               _ = (p^(k + 1) + q^(k + 1) + r^(k+1)) + p^k * q + p^k * r + p * q^k + q^k * r + p * r^k + q * r^k := by ring
               _ = s (k + 1) + p^k * q + p^k * r + p * q^k + q^k * r + p * r^k + q * r^k := by rw [hs]

  -- Using $pqr = 13$ and $s_{k} = p^{k} + q^{k} + r^{k}$, we see $13s_{k} = p^{k}qr +
  -- pq^{k}r + pqr^{k}$.
  have h2 (k) :=
    calc 13 * s k = (p * q * r) * (p^k + q^k + r^k) := by rw [pqr_mul, hs]
                _ = p^(k + 1) * q * r + p * q^(k + 1) * r + p * q * r^(k + 1) := by ring

  -- We have
  have h3 (k) :=
    calc 5 * s (k + 2) + 13 * s k = s (k + 3) + (p^(k + 2) * q + p^(k + 2) * r + p^(k + 1) * q * r) + (p * q^(k + 2) + p * q^(k + 1) * r + q^(k + 2) * r) + (p * q * r^(k + 1) + p * r^(k + 2)+ q * r^(k + 2)) := by nth_rw 1 [h1 (k + 2), h2 k]; ring
                                _ = s (k + 3) + p^(k + 1) * (p * q + p * r + q * r) + q^(k + 1) * (p * q + p * r + q * r) + r^(k + 1) * (p * q + p * r + q * r) := by ring
                                _ = s (k + 3) + (p^(k + 1) + q^(k + 1) + r^(k + 1)) * (p * q + p * r + q * r) := by ring
                                _ = s (k + 3) + 8 * s (k + 1) := by rw [pqr_two_sum, ←hs]; ring

  -- Rearrange to get $s_{k+3} = 5s_{k+2} - 8s_{k+1} + 13s_{k}$
  have h4 (k) : s (k + 3) = 5 * s (k + 2) - 8 * s (k + 1) + 13 * s k := by linarith only [h3 k]

  -- To conclude that $a = 5$, $b = -8$, and $c = 13$, we use a uniqueness argument.

  -- Let $A$ be the matrix $\begin{pmatrix} s_2 & s_1 & s_0 \\ s_3 & s_2 & s_1 \\ s_4 & s_3 & s_2
  -- \end{pmatrix}$.
  let A := Matrix.of !![s 2, s 1, s 0; s 3, s 2, s 1; s 4, s 3, s 2]
  let A := Matrix.of !![s 2, s 3, s 4; s 1, s 2, s 3; s 0, s 1, s 2]

  -- Let $u$ be the column vector $\begin{pmatrix} s_3 \\ s_4 \\ s_5 \end{pmatrix}$.
  let u := Matrix.of !![s 3, s 4, s 5]

  -- Let $x_1$ be the column vector $\begin{pmatrix} 5 \\ -8 \\ 13 \end{pmatrix}$.
  let x1 := Matrix.of !![(5:ℝ), -8, 13]

  -- Let $x_2$ be the column vector $\begin{pmatrix} a \\ b \\ c \end{pmatrix}$.
  let x2 := Matrix.of !![a, b, c]

  -- We have $s_0 = 3$ by definition.
  have hs0 : s 0 = 3 := by simp [hs]; norm_num

  -- We have $s_1 = p + q + r = 5$
  have hs1 : s 1 = 5 := by simp [hs, pqr_sum]

  -- We have $s_2 = p^2 + q^2 + r^2 = (p + q + r)^2 - 2(pq + pr + qr) = 9$.
  have hs2 : s 2 = 9 := by
    calc _ = p^2 + q^2 + r^2 := by simp [hs]
         _ = (p + q + r)^2 - 2 * (p * q + p * r + q * r) := by ring
         _ = _ := by simp [pqr_sum, pqr_two_sum]; norm_num

  -- And we find $s_3$ as 44 from $s_0$, $s_1$, $s_2$ using the recurrence relation we found earlier.
  have hs3 : s 3 = 44 := by rw [h4, hs2, hs1, hs0]; norm_num

  -- And we find $s_4$ as 213 from $s_1$, $s_2$, $s_3$ using the recurrence relation we found earlier.
  have hs4 : s 4 = 213 := by rw [h4, hs2, hs1, hs3]; norm_num

  -- And we find $s_5$ as 830 from $s_2$, $s_3$, $s_4$ using the recurrence relation we found earlier.
  have hs5 : s 5 = 830 := by rw [h4, hs2, hs3, hs4]; norm_num

  have (x y : ℝ) : Mul.mul x y = x * y := by exact rfl

  -- By assumption, we have $A x_1 = u$.
  have hx1A : x1 * A = u := by
    ext i j
    simp [Fin.fin_one_eq_zero i, Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    match j with
    | 0 | 1 | 2 => simp [x1, A, u, hs0, hs1, hs2, hs3, hs4, hs5]; norm_num

  -- Also, we just showed that $A x_2 = u$.
  have hx2A : x2 * A = u := by
    ext i j
    simp [Fin.fin_one_eq_zero i, Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    match j with
    | 0 | 1 | 2 => simp [x2, A, u, habc]

  -- Subtracting the two equations, we get $A (x_1 - x_2) = 0$.
  have x_sub_mul_A_eq_zero : (x1 - x2) * A = !![0, 0, 0] := by
    rw [Matrix.sub_mul, hx1A, hx2A, sub_self]
    ext _ j
    simp
    match j with
    | 0 | 1 | 2 => simp

  -- The determinant of $A$ is $(s_2)^3 - 2 s_1 s_2 s_3 + (s_1)^2 s_4 + s_0 (s_3)^2 - s_0 s_2 s_4$.
  have hAdet : A.det = (s 2)^3 - 2 * (s 1) * (s 2) * (s 3) + (s 1)^2 * (s 4) + (s 0) * (s 3)^2 - (s 0) * (s 2) * (s 4) := by
    rw [Matrix.det_fin_three]
    simp [A]
    ring

  -- Therefore, computing the the determinant of $A$, we see that it is invertable.
  replace hAdet : A.det ≠ 0 := by
    rw [hAdet, hs2, hs1, hs0, hs3, hs4]
    norm_num

  -- So, the equation $A (x_1 - x_2) = 0$ implies $x_1 = x_2$.
  have :=
    calc x1 - x2 = (x1 - x2) * (1 : Matrix _ _ ℝ) := by simp
               _ = (x1 - x2) * (A * A⁻¹) := by congr; symm; apply Matrix.mul_nonsing_inv; exact Ne.isUnit hAdet
               _ = ((x1 - x2) * A) * A⁻¹ := by rw [Matrix.mul_assoc]
               _ = (0 : Matrix _ _ ℝ) * A⁻¹ := by rw [x_sub_mul_A_eq_zero]; congr; ext _ j; match j with | 0 | 1 | 2 => simp
               _ = 0 := by simp
  have : x1 = x2 :=
    calc _ = x1 - x2 + x2 := by simp
         _ = 0 + x2 := by rw [this]
         _ = x2 := by simp

  -- Therefore, $a = 5$, $b = -8$, and $c = 13$.
  simp [x1, x2] at this
  split_ands
  · calc _ = !![a, b, c] 0 0 := by simp
         _ = !![5, -8, 13] 0 0 := by rw [this]
         _ = _ := by simp
  · calc _ = !![a, b, c] 0 1 := by simp
         _ = !![5, -8, 13] 0 1 := by rw [this]
         _ = _ := by simp
  · calc _ = !![a, b, c] 0 2 := by simp
         _ = !![5, -8, 13] 0 2 := by rw [this]
         _ = _ := by simp