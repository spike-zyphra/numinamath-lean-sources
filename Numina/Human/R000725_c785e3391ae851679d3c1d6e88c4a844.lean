import Mathlib

/- Let $k$ and $m$ be real numbers, and suppose that the roots of the equation \[x^3 - 7x^2 + kx - m = 0\]are three distinct positive integers. Compute $k + m.$-/
theorem algebra_14310 (k m : ℝ) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (y : Cubic ℝ) (hy : y = ⟨1, -7, k, -m⟩) (φ : ℝ →+* ℝ) (hφ : φ = RingHom.id ℝ)
    (hroots : (Cubic.map φ y).roots = ({(a : ℝ), (b : ℝ), (c : ℝ)} : Multiset ℝ)) :
    k + m = 22 := by
  -- We use `Cubic` to represent cubic polynomial $f(x)=x^3-7x^2+kx-m$.
  have hmapy : Cubic.map φ y = y := by
    rw [hφ, Cubic.map]
    ext <;> simp
  -- Since a,b,c are roots of $f(x)$, we have $f(x)=(x-a)(x-b)(x-c)$.
  have := Cubic.eq_prod_three_roots (show y.a ≠ 0 by simp [hy]) hroots
  rw [Cubic.C_mul_prod_X_sub_C_eq, Cubic.toPoly_injective, hmapy] at this
  -- Hence we have a+b+c=7
  have habc : a + b + c = 7 := by
    apply_fun (·.b) at this
    simp [hφ, hy] at this
    rify
    linear_combination this
  -- Similiarly, we have k=ab+ac+bc.
  have hk : k = a * b + a * c + b * c := by
    apply_fun (·.c) at this
    simp [hφ, hy] at this
    exact this
  -- We have m=abc.
  have hm : m = a * b * c := by
    apply_fun (·.d) at this
    simp [hφ, hy] at this
    exact this
  -- Since a,b,c are positive integers, there must be a,b,c=1,2,4.
  have ⟨ha1, hb1, hc1⟩ : a < 5 ∧ b < 5 ∧ c < 5 := by split_ands <;> omega
  interval_cases a <;> interval_cases b <;> interval_cases c
  any_goals norm_num at hab
  any_goals norm_num at hbc
  any_goals norm_num at hca
  any_goals norm_num at habc
  -- Hence k+m=22 holds true.
  all_goals norm_num [hk, hm]
