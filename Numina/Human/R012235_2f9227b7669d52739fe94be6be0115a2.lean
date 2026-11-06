import Mathlib

--set_option maxRecDepth 10000

-- 18. In how many ways can the number 1024 be factored into three natural factors such that the first factor is divisible by the second, and the second is divisible by the third?
theorem number_theory_194174 :
    {(a, b, c) : ℕ × ℕ × ℕ | a * b * c = 1024 ∧ b ∣ a ∧ c ∣ b}.ncard = 14 := by
  /-
  Ответ: 14

  Решение: Заметим, что множители имеют вид $2^{a} \times 2^{b} \times 2^{c}$, где $\mathrm{a}+\mathrm{b}+\mathrm{c}=10$ и $a \geq b \geq c$. Очевидно, что с меньше 4,т.к. сумма была бы больше 10. Рассмотрим случаи:

  $c=0)$ Тодга $b=0, \ldots, 5, a=10-b-6$ вариантов

  c=1) Тогда $b=1, . .4, a=9-b-4$ вар.

  $c=2) b=2,3,4, a=8-b-3$ вар.

  $c=3) b=3, a=4-1$ вар.

  итого $6+4+3+1=14$ вариантов.
  -/
  let f : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
    | (p, q, r) => (2 ^ p, 2 ^ q, 2 ^ r)
  let f_embedding := Function.Embedding.mk f (by simp [Function.Injective, f])
  let t := (Finset.range 4).biUnion fun c =>
    let d := (10 - c)
    ((Finset.Icc c d).map ⟨fun b => (d - b, b, c), by simp [Function.Injective, f]⟩
    ).filter (fun (a, b, _) => a ≥ b)
  set s := {(a, b, c) : ℕ × ℕ × ℕ | a * b * c = 1024 ∧ b ∣ a ∧ c ∣ b}
  have : s = t.map f_embedding := by
    simp [s, t, f_embedding, f]
    ext ⟨a, b, c⟩
    simp
    constructor
    . rintro ⟨mul_eq_1024, b_dvd_a, c_dvd_b⟩
      have prime_2 := Nat.prime_two
      rw [show 1024 = 2 ^ 10 by simp] at mul_eq_1024
      have : ∃ p ≤ 10, a = 2 ^ p := by
        have : a ∣ 2 ^ 10 := by
          have : a * (b * c) = 2 ^ 10 := by linarith
          exact Dvd.intro (b * c) this
        exact (Nat.dvd_prime_pow prime_2).mp this
      rcases this with ⟨p, p_le_10, a_eq⟩
      have := by
        have : b ∣ 2 ^ 10 := by
          have : b * (a * c) = 2 ^ 10 := by linarith
          exact Dvd.intro (a * c) this
        exact (Nat.dvd_prime_pow prime_2).mp this
      rcases this with ⟨q, q_le_10, b_eq⟩
      have := by
        have : c ∣ 2 ^ 10 := by
          have : c * (a * b) = 2 ^ 10 := by linarith
          exact Dvd.intro (a * b) this
        exact (Nat.dvd_prime_pow prime_2).mp this
      rcases this with ⟨r, r_le_10, c_eq⟩
      use p, q, r
      constructor
      . use r
        subst a_eq b_eq c_eq
        have : p + q + r = 10 := by
          --rw [a_eq, b_eq, c_eq] at mul_eq_1024
          rw [show 2 ^ p * 2 ^ q * 2 ^ r = 2 ^ (p + q + r) by ring] at mul_eq_1024
          have : 2 ≤ 2 := by simp
          --apply?
          exact Nat.pow_right_injective this mul_eq_1024
        have : r ≤ q := by
          exact Nat.pow_dvd_pow_iff_le_right'.mp c_dvd_b
        have : q ≤ p := by
          exact Nat.pow_dvd_pow_iff_le_right'.mp b_dvd_a
        constructor
        . use q
          omega
        . omega
      . omega
    . rintro ⟨
        p, q', r',
        ⟨
          ⟨r, ⟨q, ⟨r_le_q, q_le_10_sub_r⟩, _10_sub_r_sub_q_eq_p, rfl, rfl⟩, r_lt_4, q_le_p⟩,
          ⟨rfl, rfl, rfl⟩
        ⟩
      ⟩
      constructor
      . rw [show 2 ^ p * 2 ^ q * 2 ^ r = 2 ^ (p + q + r) by ring]
        have : p + q + r = 10 := by
          omega
        rw [this]
        rfl
      constructor
      . exact Nat.pow_dvd_pow_iff_le_right'.mpr q_le_p
      . exact Nat.pow_dvd_pow_iff_le_right'.mpr r_le_q
  have : s.ncard = t.card := by
    rw [this]
    simp
  rw [this]
  rfl
