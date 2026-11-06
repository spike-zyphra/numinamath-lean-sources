import Mathlib

set_option maxHeartbeats 20000000

/- Let $k$ be a positive integer. Find all pairs of positive integers $(x, y)$ such that
$$ \frac{1}{x}+\frac{1}{y}+\frac{1}{\operatorname{lcm}(x, y)}+\frac{1}{\operatorname{gcd}(x, y)}=\frac{1}{k} $$
Let $g = \operatorname{gcd}(x,y)$, $x=ga$ and $y=gb$ where $a,b$ are coprime positive integers. The equation transforms to $k(a+1)(b+1)=gab$. The solutions $(x,y)$ are of the form $(ga, gb)$ where $g = k \frac{(a+1)(b+1)}{ab}$ is an integer, for coprime $a,b$.

For $k=1$, the solutions $(x,y)$ (up to symmetry) are:
1. If $a=1, b=1$: $g = 1 \cdot \frac{2 \cdot 2}{1 \cdot 1} = 4$. So $(x,y)=(4,4)$.
2. If $a=1, b=2$: $g = 1 \cdot \frac{2 \cdot 3}{1 \cdot 2} = 3$. So $(x,y)=(3,6)$.
3. If $a=2, b=3$: $g = 1 \cdot \frac{3 \cdot 4}{2 \cdot 3} = 2$. So $(x,y)=(4,6)$.
Thus, for $k=1$, the pairs are $(4,4), (3,6), (6,3), (4,6), (6,4)$. -/
theorem number_theory_635032
  {k : ℕ} (hk : k > 0)
  (x y : ℕ) (xpos : x > 0) (ypos : y > 0)
  : 1/x + 1/y + 1/x.lcm y+ 1/x.gcd y = (1/k : ℚ) ↔
    ∃ a b : ℕ, a.Coprime b ∧ (x.gcd y : ℚ) = k*(a + 1)*(b+1)/(a*b) ∧ x = x.gcd y * a ∧ y = x.gcd y * b :=
by

  -- The whole idea of the proof is simply transform the given equations and get the goal form.

  constructor
  . -- → direction, generate the solutions
    intro H
    have H' := H
    field_simp at H
    apply_fun (fun i => (i * x.lcm y * x.gcd y : ℚ)) at H
    have : x.lcm y > 0 := by exact Nat.lcm_pos xpos ypos
    have : x.gcd y > 0 := by exact Nat.gcd_pos_of_pos_left y xpos
    field_simp at H
    ring_nf at H
    let g := x.gcd y
    have ⟨a, b, copab, xga, ygb⟩ : ∃ a b, a.Coprime b ∧ x = g * a ∧ y = g * b := by
      use x / g, y / g
      constructor
      . simp [g]
        exact Nat.coprime_div_gcd_div_gcd this
      constructor
      . qify
        rw [Int.cast_div]
        push_cast
        field_simp
        simp [g]
        norm_cast
        exact Nat.gcd_dvd_left x y
        norm_cast
        simp [g]
        omega
      . qify
        rw [Int.cast_div]
        push_cast
        field_simp
        simp [g]
        norm_cast
        exact Nat.gcd_dvd_right x y
        norm_cast
        simp [g]
        omega
    use a, b
    constructor
    . assumption
    have : (x.lcm y : ℚ) = x * y / g := by
      simp [g]
      field_simp
      norm_cast
      rw [←Nat.gcd_mul_lcm x]
      linarith
    rw [this] at H'
    rw [show x.gcd y = g by rfl] at H'
    rw [xga, ygb] at H'
    push_cast at H'
    have : (1 / (g * a) + 1 / (g * b) + 1 / (g * a * (g * b) / g) + 1 / g : ℚ)
         = 1/g * (1 / a + 1 / b + 1 / (a * b) + 1) := by
      have : g > 0 := by simp [g]; assumption
      field_simp
      ring_nf
      have : (g * (g : ℚ)⁻¹ : ℚ) = 1 := by
        field_simp
      field_simp
      ring_nf
    rw [this] at H'
    have : (1 / a + 1 / b + 1 / (a * b) + 1 : ℚ) = (a + 1) * (b + 1) / (a * b) := by
      ring_nf
      have h1 : (a * (a : ℚ)⁻¹ : ℚ) = 1 := by
        apply Rat.mul_inv_cancel
        intro c
        norm_cast at c
        subst c
        omega
      have h2 : (b * (b : ℚ)⁻¹ : ℚ) = 1 := by
        apply Rat.mul_inv_cancel
        intro c
        norm_cast at c
        subst c
        omega
      rw [h1]
      simp
      rw [mul_assoc, h2]
      simp
      linarith
    rw [this] at H'
    field_simp at H'
    have H' : (a + 1) * (b + 1) * k = g * a * b := by
      qify
      apply_fun (fun x => x * (g * (a * b) : ℚ)) at H'
      rw [div_mul, div_self] at H'
      simp at H'
      linarith
      simp
      constructor
      . omega
      constructor
      . intro c
        subst c
        omega
      . intro c
        subst c
        omega
    constructor
    . simp [g] at H'
      have : (a * b : ℚ) > 0 := by
        norm_cast
        by_contra h
        simp at h
        have : a > 0 := by
          by_contra h
          simp at h
          subst h
          omega
        have : b = 0 := by
          tauto
        subst this
        omega
      field_simp
      qify at H'
      linarith
    constructor
    <;> simp only [g] at *
    <;> omega
  . -- ← direction, test solution
    intro ⟨a, b, copab, H, xeq, yeq⟩
    apply_fun (fun i => (i / (k * x.gcd y): ℚ)) at H
    conv at H =>
      lhs
      rw [mul_comm, ←div_div]
    rw [div_self] at H
    have : ↑k * (↑a + 1) * (↑b + 1) / (↑a * ↑b) / (↑k * ↑(x.gcd y) : ℚ)
         = (↑a + 1) * (↑b + 1) / (↑a * ↑b) / ↑(x.gcd y) := by
      have : (k : ℚ) ≠ 0 := by norm_cast; omega
      field_simp
      have : ↑k * (↑a + 1) * (↑b + 1) / (↑a * ↑b * (↑k * ↑(x.gcd y)) : ℚ) = (↑k / k) * (↑a + 1) * (↑b + 1) / (↑a * ↑b * (↑(x.gcd y))) := by
        ring_nf
      rw [this]
      rw [div_self]
      simp
      assumption
    rw [this] at H
    have : (↑a + 1) * (↑b + 1) / (↑a * ↑b : ℚ) = 1/a + 1/b + 1/(a*b) + 1 := by
      ring_nf
      have h1 : (a * (a : ℚ)⁻¹ : ℚ) = 1 := by
        apply Rat.mul_inv_cancel
        intro c
        norm_cast at c
        subst c
        omega
      have h2 : (b * (b : ℚ)⁻¹ : ℚ) = 1 := by
        apply Rat.mul_inv_cancel
        intro c
        norm_cast at c
        subst c
        omega
      conv =>
        lhs
        rw [mul_comm (a : ℚ), mul_assoc (b : ℚ), h1]
        simp
        rw [h2]
        rw [mul_comm (b : ℚ), mul_assoc (a⁻¹ : ℚ), h2]
        simp
      ring_nf
    rw [this] at H
    rw [H]
    have : (x.lcm y : ℚ) = x * y / x.gcd y := by
      norm_cast
      rw [←Nat.gcd_mul_lcm x]
      have : (x.gcd y : ℚ) ≠ 0 := by
        norm_cast
        refine Nat.ne_zero_iff_zero_lt.mpr ?_
        exact Nat.gcd_pos_of_pos_left y xpos
      field_simp
    rw [this]
    generalize h : x.gcd y = g
    have : (g : ℚ) ≠ 0 := by
      subst h
      norm_cast
      refine Nat.ne_zero_iff_zero_lt.mpr ?_
      exact Nat.gcd_pos_of_pos_left y xpos
    have : (a : ℚ) ≠ 0 := by
      norm_cast
      intro c
      subst c
      omega
    have : (b : ℚ) ≠ 0 := by
      norm_cast
      intro c
      subst c
      omega

    rw [h] at xeq yeq
    rw [xeq, yeq]
    push_cast
    have : 1 / (↑g * ↑a * (↑g * ↑b) / ↑g : ℚ) = 1 / (↑g * ↑a * ↑b) := by
      field_simp
      ring_nf
    rw [this]
    ring_nf
    norm_cast
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    exact Nat.gcd_pos_of_pos_left y xpos
