import Mathlib

/- The greatest common divisor of positive integers $m$ and $n$ is 8.
The least common multiple of $m$ and $n$ is 112. What is the least possible value of $m+n$? -/
theorem number_theory_19279 :
    IsLeast {x | ∃ m n, x = m + n ∧ m > 0 ∧ n > 0 ∧
    Nat.gcd m n = 8 ∧ Nat.lcm m n = 112} 72 := by
  -- if gcd of m and n is 8, then we can find x,y such that m=8x, n=8y and x,y coprime
  have h1(m n: ℕ)(hgcd: m.gcd n = 8): ∃(x y: ℕ), m = 8*x ∧ n = 8*y
    ∧ Nat.Coprime x y := by
    have := Nat.exists_coprime m n
    rcases this with ⟨x,y,hxy⟩
    use x, y
    rw [hgcd] at hxy; simp [hxy]; ring_nf
    simp
    exact hxy.left
  -- therefore lcm of m and n is 8 lcm x y = 8xy
  have h2{m n x y:ℕ}(hcop: Nat.Coprime x y)(hm: m = 8*x)(hn: n = 8*y): Nat.lcm m n = 8 * x * y := by
    rw [hm, hn]
    rw [Nat.lcm_mul_left]
    rw [Nat.Coprime.lcm_eq_mul hcop]
    ring
  -- notice that 112 = 8x14, so if 8xy = 112, then xy = 14.
  -- least possible value of x+y is 7+2 = 9
  have h3{x y:ℕ}(h1: 8*x*y = 112)(h2: Nat.Coprime x y): x+y ≥ 9 := by
    have hh1: x*y = 14 := by linarith [h1]
    have hh2: x ≥ 1 := by
      by_contra! hc
      interval_cases x; simp at hh1
    have hh3: y ≥ 1 := by
      by_contra! hc
      interval_cases y; simp at hh1
    have hh4: x ≤ 14 := by
      rw [← hh1]
      exact Nat.le_mul_of_pos_right x hh3
    have hh5: x ∣ 14 := by
      rw [← hh1]
      exact Nat.dvd_mul_right x y
    -- factors of 14 are 1,2,7,14
    have dv14: ∀m:ℕ, m ≥ 1 → m ≤ 14 → m ∣ 14 → (m = 1 ∨ m = 2 ∨ m = 7 ∨ m = 14)
      := by decide
    rcases (dv14 x hh2 hh4 hh5) with hhx | hhx | hhx | hhx
    <;> rw [hhx] <;> rw [hhx] at hh1
    <;> linarith [hh1]
  -- x+y=9, so m=56,n=16,m+n=72. answer is 72
  rw [IsLeast, lowerBounds]; simp; constructor
  · use 56, 16; norm_num
  · intro u m n hu _ _ hgcd hlcm
    rcases (h1 m n hgcd) with ⟨x,y,hxy⟩
    rw [h2 hxy.right.right hxy.left hxy.right.left] at hlcm
    have h4 := h3 hlcm hxy.right.right
    rw [hu, hxy.left, hxy.right.left]
    calc
      _ = 8*9 := by norm_num
      _ ≤ 8 * (x+y) := by linarith [h4]
      _ = _ := by ring