import Mathlib

open Nat
open scoped Pointwise

-- Prove an auxiliary lemma: {a, b} * s = {a} * s ∪ {b} * s for any finset s.
lemma Finset.pair_mul (a b : ℕ) (s : Finset ℕ) : {a, b} * s = {a} * s ∪ {b} * s := by
  have eq : {a, b} = {a} ∪ ({b} : Finset ℕ) := by ext n; simp
  rw [eq, Finset.union_mul]

-- Prove an auxiliary lemma: {a} * s = s.image (a * ·) for any finset s.
lemma Finset.singleton_mul' (a : ℕ) (s : Finset ℕ) : {a} * s = s.image (a * ·) := by
  ext n
  simp [Finset.mem_mul]

-- Show that if p1 and p2 are prime numbers then
-- p1^2 + p2^2 = p3 * (p1 + p2) implies that p1 = p2 = p3.
lemma lemma_1 {p1 p2 p3 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (h : p1 ^ 2 + p2 ^ 2 = p3 * (p1 + p2)) :
    p1 = p2 ∧ p2 = p3 := by
  -- It is enough to show that p1 = p2.
  suffices p1 = p2 by
    simp [this] at h ⊢
    -- Indeed, if p1 = p2 then 2 * p2 * p2 = 2 * p2 * p3.
    have eq : 2 * p2 * p2 = 2 * p2 * p3 := by linear_combination h
    -- It follows that p2 = p3.
    apply Nat.mul_left_cancel _ eq
    linarith [hp2.two_le]
  -- Show that p1 + p2 divides 2 * p1 * p2.
  have hdvd : p1 + p2 ∣ 2 * p1 * p2 := by
    -- It is enough to show that 2 * p1 * p2 = (p1 + p2) * ((p1 + p2) - p3).
    use (p1 + p2) - p3
    rw [Nat.mul_sub, mul_comm _ p3, ←h]
    ring_nf
    omega
  -- Show that divisors of 2 * p1 * p2 are {p2, p2 * 2, p2 * p1, 1, 2, p1, 2 * p1, p2 * (2 * p1)}.
  have hdiv : (2 * p1 * p2).divisors = {p2, p2 * 2, p2 * p1, 1, 2, p1, 2 * p1, p2 * (2 * p1)} := by
    -- We have (n * m).divisors = n.divisors * m.divisors for any m and n
    -- (here we have the pointwise set product on the right hand side).
    -- For any prime number p, we have (p).divisors = {1, p}.
    rw [divisors_mul, divisors_mul, hp1.divisors, hp2.divisors, prime_two.divisors]
    -- Show that {1, 2} * {1, p1} = {1, 2, p1, 2 * p1}.
    have eq1 : {1, 2} * {1, p1} = ({1, 2, p1, 2 * p1} : Finset ℕ) := by
      simp_rw [Finset.pair_mul, Finset.singleton_mul']
      ext n
      simp
      tauto
    -- Show that {1, p2} * {1, 2, p1, 2 * p1} = {p2, p2 * 2, p2 * p1, 1, 2, p1, 2 * p1, p2 * (2 * p1)}.
    rw [eq1, mul_comm, Finset.pair_mul]
    simp_rw [Finset.singleton_mul']
    ext n
    simp only [one_mul, Finset.image_insert, Finset.image_singleton, mul_one, Finset.union_insert,
      Finset.insert_union, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  -- We get p1 + p2 ∈ (2 * p1 * p2).divisors.
  replace hdvd : p1 + p2 ∈ (2 * p1 * p2).divisors := by
    simp [hdvd, hp1.ne_zero, hp2.ne_zero]
  -- Consider all possible cases for p1 + p2.
  simp [hdiv] at hdvd
  rcases hdvd with h | h | h | h | h | h | h | h
  -- p1 ≠ 0.
  · simp [hp1.ne_zero] at h
  -- p1 + p2 = p2 * 2 implies p1 = p2.
  · omega
  -- p1 + p2 = p2 * p1 implies that p1 = p2 = 2 (since any prime number >= 2).
  · nlinarith [hp1.two_le, hp2.two_le]
  -- p1 + p2 ≠ 1.
  · linarith [hp1.two_le]
  -- p1 + p2 ≠ 2.
  · linarith [hp1.two_le, hp2.two_le]
  -- p2 ≠ 0.
  · simp [hp2.ne_zero] at h
  -- p1 + p2 = 2 * p1 implies that p1 = p2.
  · omega
  -- p1 + p2 = p2 * (2 * p1) is impossible since
  -- 2 * p2 * p1 > p2 * p1 ≥ p1 + p2.
  · nlinarith [hp1.two_le, hp2.two_le]

-- Show that if p is prime and p^3 - 8 is prime then p = 3.
lemma lemma_2 {p : ℕ} (hp : p.Prime) (hp2 : (p * p * p - 8).Prime) : p = 3 := by
  -- 2 ≤ p.
  have hle2 := hp.two_le
  -- p^3 - 8 = (p - 2) * (p^2 + 2 * p + 4).
  have eq : p * p * p - 8 = (p - 2) * (p * p + 2 * p + 4) := by
    have : 8 ≤ p * p * p := calc
      2^3 ≤ p^3 := by apply pow_le_pow hle2 hp.one_le (le_refl _)
      _ = p * p * p := by ring
    zify [hle2, this]
    ring
  -- (p - 2) * (p^2 + 2 * p + 4) is prime so either
  -- p - 2 = 1 or p^2 + 2 * p + 4 = 1.
  -- We have p^2 + 2 * p + 4 > 1, so p - 2 = 1 and p = 3.
  rw [eq, prime_mul_iff] at hp2
  cases' hp2 <;> omega

/- ## Task 13/90
Determine all solutions of the system of equations
$$
p_{1}^{2}+p_{2}^{2}=p_{3}\left(p_{1}+p_{2}\right) \quad(1) \quad ; \quad p_{1} p_{2} p_{3}-8=p_{4}
$$
in prime numbers $p_{i}(i=1 ; 2 ; 3 ; 4)$. -/
theorem number_theory_161501 (p : Fin 4 → ℕ) :
    (∀ i, Nat.Prime (p i)) ∧ (p 0 ^ 2 + p 1 ^ 2 = p 2 * (p 0 + p 1)) ∧ (p 0 * p 1 * p 2 - 8 = p 3) ↔
    p 0 = 3 ∧ p 1 = 3 ∧ p 2 = 3 ∧ p 3 = 19 := by
  symm
  constructor
  -- Show that p0 = p1 = p2 = 3 and p3 = 19 satisfy all conditions.
  · intro ⟨p0, p1, p2, p3⟩
    rw [p0, p1, p2, p3]
    norm_num
    intro i
    fin_cases i <;> simp [p0, p1, p2, p3] <;> norm_num
  -- Assume that p0^2 + p1^2 = p2 * (p0 + p1) and p0 * p1 * p2 - 8 = p3.
  -- Show that p0 = p1 = p2 = 3 and p3 = 19.
  intro ⟨hp, h1, h2⟩
  -- lemma_1 implies that p0 = p1 = p2.
  have ⟨h01, h12⟩ := lemma_1 (hp 0) (hp 1) h1
  -- h2 becomes p0^3 - 8 = p3.
  rw [← h12, ← h01] at h2
  -- lemma_2 implies that p0 = 3.
  have h0 := lemma_2 (hp 0) (h2 ▸ hp 3)
  -- We conclude that p0 = p1 = p2 = 3 and p3 = p0^3 - 8 = 27 - 8 = 19.
  rw [h0] at h2
  omega