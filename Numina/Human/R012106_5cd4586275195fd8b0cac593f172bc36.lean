import Mathlib

/- Trouver toutes les fonctions $\mathrm{f}: \mathbb{N} \rightarrow \mathbb{N}$ telles que

$$
x f(y)+y f(x)=(x+y) f\left(x^{2}+y^{2}\right)
$$

pour tous les entiers naturels $x$ et $y$.
Note : on rappelle que $\mathbb{N}$ désigne l'ensemble des entiers naturels, c'est-à-dire $\mathbb{N}=\{0,1,2, \ldots\}$. -/
theorem algebra_605662 {f : ℕ → ℕ}:
  (∀ x y, x * f y + y * f x = (x + y) * f (x ^ 2 + y ^ 2)) ↔
  (∀ x, f x = f 0) := by
  constructor <;> intro h
  · -- from the given equation, take (x,y) = (x,0).
    -- we have x f0 = x f(x^2), or, f(x^2) = f(0).
    have h1(x:ℕ): f (x^2) = f 0 := by
      have := h x 0
      simp only [zero_mul, add_zero, pow_two] at this
      by_cases hx: x = 0
      · simp [hx]
      rw [pow_two]; symm
      exact (Nat.mul_right_inj hx).mp this
    -- then, take (x,y) = (3n^2, 4n^2), we can prove f(3n^2) = f(0)
    have h2(n:ℕ): f (3*n^2) = f 0 := by
      have hh1 := h (3*n^2) ((2*n)^2)
      have hh2: (3*n^2)^2 + ((2*n)^2)^2 = (5*n^2)^2 := by ring
      rw [hh2, h1 (2*n), h1 (5*n^2), Nat.add_mul] at hh1
      by_cases hn: n = 0
      · simp [hn]
      rw [add_right_inj, mul_eq_mul_left_iff] at hh1
      rcases hh1 with hh | hh
      · exact hh
      · simp [hn] at hh
    -- take (x,y) = (12n^2, 5n^2), f(5n^2) = f(0)
    have h3(n:ℕ): f (5*n^2) = f 0 := by
      have hh1 := h (12*n^2) (5*n^2)
      have hh2: (12*n^2)^2 + (5*n^2)^2 = (13*n^2)^2 := by ring
      have hh3: f (12*n^2) = f (3 * (2*n)^2) := by ring_nf
      rw [hh3, hh2, h1, h2, Nat.add_mul] at hh1
      rw [add_left_inj, mul_eq_mul_left_iff] at hh1
      by_cases hn: n = 0
      · simp [hn]
      rcases hh1 with hh | hh
      · exact hh
      · simp [hn] at hh
    -- take (x,y) = (2n^2, n^2), f(2n^2) = f(0).
    have h4(n:ℕ): f (2*n^2) = f 0 := by
      have hh1 := h (2*n^2) (n^2)
      have hh2: (2*n^2)^2 + (n^2)^2 = 5*((n^2)^2) := by ring
      rw [hh2, h3, h1, Nat.add_mul, add_right_inj] at hh1
      by_cases hn: n^2 = 0
      · simp [hn]
      exact (Nat.mul_right_inj hn).mp hh1
    -- finally, take x=y. done.
    intro x
    have := h x x
    simp only [← two_mul, h4, ← mul_assoc] at this
    by_cases hx: x = 0
    · simp [hx]
    apply (Nat.mul_right_inj ?_).mp this
    simp [hx]
  · -- verification.
    intro x y
    rw [h y, h x, h (x^2+y^2), Nat.add_mul]