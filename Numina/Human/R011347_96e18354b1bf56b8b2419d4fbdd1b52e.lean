import Mathlib

/- Consider the sequence

$$
\begin{aligned}
x_{1} & =19, \\
x_{2} & =95, \\
x_{n+2} & =\operatorname{lcm}\left(x_{n+1}, x_{n}\right)+x_{n},
\end{aligned}
$$

for $n≥1$, where $\operatorname{lcm}(a, b)$ means the least common multiple of $a$ and $b$. Find the greatest common divisor of $x_{1995}$ and $x_{1996}$. -/
theorem number_theory_239043 (x : ℕ → ℕ)
    (hx1 : x 1 = 19)
    (hx2 : x 2 = 95)
    (hxn : ∀ n ≥ 1, x (n + 2) = Nat.lcm (x (n + 1)) (x n) + x n) :
    Nat.gcd (x 1995) (x 1996) = 19 := by
  have x_pos : ∀ n ≥ 1, x n > 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        cases n with
        | zero => tauto
        | succ n =>
            simp
            have h1 := ih n (by linarith)
            have h2 := ih (n - 1) (by omega)
            by_cases h3: n ≥ 2
            replace h1: x n > 0 := by apply h1;omega
            replace h2: x (n - 1) > 0 := by apply h2;omega
            have h4 : Nat.lcm (x n) (x (n - 1)) > 0 := by
              simp
              apply Nat.lcm_pos
              tauto
              tauto
            have y := hxn (n - 1) (by omega)
            replace y: x (n + 1) = (x n).lcm (x (n - 1)) + x (n - 1) := by
              calc
                x (n + 1) = x (n - 1 + 1 + 1) := by rw [Nat.sub_add_cancel]; omega
                        _ = x (n - 1 + 2) := by rw [Nat.add_assoc]
                        _ = (x (n - 1 + 1)).lcm (x (n - 1)) + x (n - 1) := by exact y
                        _ = (x n).lcm (x (n - 1)) + x (n - 1) := by rw [Nat.sub_add_cancel]; omega
            linarith
            simp at h3
            have u: (n = 1) ∨ (n = 0) := by omega
            rcases u with p | q
            . simp [p,hx2]
            . simp [q,hx1]
  have eq: ∀ k ≥ 1, Nat.gcd (x (k + 1)) (x (k + 2)) = Nat.gcd (x k) (x (k + 1)) := by
    intro k hk1
    let d:= Nat.gcd (x k) (x (k + 1))
    have j: Nat.lcm (x k) (x (k + 1)) = x k * x (k + 1) / d := by
      rw [← Nat.gcd_mul_lcm (x k) (x (k + 1))]
      simp [d]
      rw [Nat.mul_div_right]
      have l: (x k).gcd (x (k + 1)) ≠ 0 := by
        by_contra! l
        rw [Nat.gcd_eq_zero_iff] at l
        rcases l with ⟨l1, l2⟩
        specialize x_pos k hk1
        omega
      omega
    have h: x (k + 2) = x k * x (k + 1) / d + x k := by
      rw [hxn k hk1]
      rw [← j]
      simp
      apply Nat.lcm_comm
    rw [h]
    have v: (x (k + 1)).gcd (x k * x (k + 1) / d + x k) = (x (k + 1)).gcd (x k + (x k / d)* x (k + 1)) := by
      ring_nf
      have t: x k * x (1 + k) / d = x (1 + k) * (x k / d) := by
        rw [Nat.mul_comm]
        rw [Nat.mul_div_assoc]
        simp [d]
        apply Nat.gcd_dvd_left
      simp [t]
    simp [v]
    rw [Nat.gcd_comm]
  have FinalEq: ∀ n ≥ 1, (x n).gcd (x (n + 1)) = 19 := by
    intro n hn
    induction' n with n ih
    . tauto
    . by_cases h: n = 0
      . simp [h,hx1,hx2]
      . have o: n ≥ 1 := by omega
        specialize eq n o
        rw [eq]
        simp [ih,o]
  exact FinalEq 1995 (by linarith)