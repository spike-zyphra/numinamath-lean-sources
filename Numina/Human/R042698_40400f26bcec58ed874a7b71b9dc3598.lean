import Mathlib
/-An integer $X$ has the following properties:

1.) $X$ is a multiple of 17

2.) $X$ is less than 1000

3.) $X$ is one less than a multiple of 8.

What is the largest possible value of $X$?-/
theorem number_theory_22983 :
    IsGreatest {x | 17 ∣ x ∧ x < 1000 ∧ (x + 1) % 8 = 0} 935 := by
      have heq : {x | 17 ∣ x ∧ x < 1000 ∧ (x + 1) % 8 = 0} = {119,255,391,527,663,799,935} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Nat.dvd_iff_mod_eq_zero]
        constructor
        .
          -- Positive proof: If x satisfies the condition, then x is in the right-hand set
          rintro ⟨h₁ : x % 17 = 0, h₂ : x < 1000, h₃ : (x + 1) % 8 = 0⟩
          --Let the desired number be $x$. Then \begin{align\*} x \equiv 0 & \pmod {17}\ x \equiv -1\equiv 7 & \pmod 8 \end{align\*} The first congruence implies that there exists a non-negative integer $n$ such that $x=17n$.
          have h₄ : ∃ n, x = 17 * n := ⟨x / 17, by omega⟩
          rcases h₄ with ⟨n, rfl⟩
          -- Substituting this into the second congruence yields $$17n\equiv 7\pmod 8,$$ $$\implies n\equiv 7\pmod 8.$$ So $n$ has a lower bound of $7$.
          have h₅ : n % 8 = 7 := by
            have : (17 * n + 1) % 8 = 0 := h₃
            simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at this
            omega
          -- If x = 8n+7, then x=17 * (8n+7)=136n+119
          have h₆ : ∃ m, n = 8 * m + 7 := ⟨(n - 7) / 8, by omega⟩
          rcases h₆ with ⟨m, rfl⟩
          -- Then $$n\ge 7,$$ $$\implies x=17n\ge 119.$$ $119$ satisfies both congruences, so subtracting it from both sides of both congruences gives \begin{align\*} x-119\equiv -119\equiv 0 &\pmod {17}\nonumber\ x-119\equiv -112\equiv 0 &\pmod 8\nonumber \end{align\*} Since $\gcd(17,8)=1$, we get $x-119\equiv 0\pmod{17\cdot 8}.$ That is, $x\equiv 119\pmod {136}.$
          have h₇ : 17 * (8 * m + 7) < 1000 := by linarith
          have h₈ : m ≤ 6 := by omega
          -- List m=0 to 6, verify that the corresponding value of x is in the set on the right
          interval_cases m
          <;> simp [h₁, h₂, h₃, Nat.mod_eq_of_lt]
        .
          -- Reverse proof: The elements in the right-hand set satisfy the original condition
          rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          <;>simp [Nat.mod_eq_of_lt, Nat.dvd_iff_mod_eq_zero]
      rw [heq,IsGreatest]; norm_num
