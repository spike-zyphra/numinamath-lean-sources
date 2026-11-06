import Mathlib.Tactic

/- According to Anna, the number 2021 is fantabulous. She states that if any element of the set
{m,2m+1,3m} is fantabulousfor for a positive integer m, then they are all fantabulous.
Is the number 2021^2021 fantabulous? (Australia, Angelo Di Pasquale) Answer: Yes -/
theorem number_theory_605597 {Fantabulous: Set ℕ} (h: ∀ m: ℕ, 1 ≤ m →
m ∈ Fantabulous ∨ 2 * m + 1 ∈ Fantabulous ∨ 3 * m ∈ Fantabulous →
m ∈ Fantabulous ∧  2 * m + 1 ∈ Fantabulous ∧  3 * m ∈ Fantabulous)
 (h1: 2021 ∈ Fantabulous): 2021 ^ 2021 ∈ Fantabulous := by
  set a := 2021 ^ 2021 with ha
  set s := Fantabulous with hs

  -- we prove the key fact
  have g: ∀ m: ℕ, 1 < m → (m ∈ s ↔ m / 2 ∈ s) := by
    intro m hm
    -- we show for the 2n + 1 case
    have l: ∀ n: ℕ, 1 ≤ n → (n ∈ s ↔ 2 * n + 1 ∈ s) := by
      intro n hn
      constructor
      . specialize h n
        simp [hn] at h
        intro o
        simp [o] at h
        simp [h]
      . specialize h n
        simp [hn] at h
        intro o
        simp [o] at h
        simp [h]
    -- we show for the 2n case
    have r: ∀ n: ℕ, 1 ≤ n → (n ∈ s ↔ 2 * n ∈ s) := by
    -- use the sequence n 3n 6m+1 12m+3 4m+1 2m --
      intro n hn
      constructor
      -- the forward direction
      . have h':= h
        specialize h n
        simp [hn] at h
        intro v
        simp [v] at h
        have s1: 3 * n ∈ s := by
          simp [h]
        clear h
        have s2: 6 * n + 1 ∈ s := by
          specialize l (3 * n)
          have o: 1 ≤ 3 * n := by omega
          simp [o] at l
          simp [s1] at l
          rw [show 2 * (3 * n) + 1 = 6 * n + 1 by ring] at l
          exact l
        have s3: 12 * n + 3 ∈ s := by
          specialize l (6 * n + 1)
          have o: 1 ≤ 6 * n + 1 := by omega
          simp [o] at l
          simp [s2] at l
          rw [show 2 * (6 * n + 1) = 12 * n + 2 by ring] at l
          exact l
        have s4: 4 * n + 1 ∈ s := by
          specialize h' (4 * n + 1)
          simp [hn] at h'
          ring_nf at h'
          rw [show 3 + n * 12 = 12 * n + 3 by ring] at h'
          simp [s3] at h'
          rw [show 4 * n + 1 = 1 + n * 4 by ring]
          simp [h']
        specialize l (2 * n)
        have o: 1 ≤ 2 * n := by omega
        simp [o] at l
        rw [l]
        rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring]
        exact s4
      -- the backward direction
      . have h':= h
        specialize h n
        simp [hn] at h
        intro v
        simp [v] at h'
        have s1: 4 * n + 1 ∈ s := by
          specialize l (2 * n)
          have o: 1 ≤ 2 * n := by omega
          simp [o] at l
          rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring] at l
          rw [← l]
          exact v
        have s2: 12 * n + 3 ∈ s := by
          specialize h' (4 * n + 1)
          simp [hn] at h'
          ring_nf at h'
          rw [show 1 + n * 4  = 4 * n + 1 by ring] at h'
          simp [s1] at h'
          rw [show 12 * n + 3 = 3 + n * 12 by ring]
          simp [h']
        have s3: 6 * n + 1 ∈ s := by
          specialize l (6 * n + 1)
          have o: 1 ≤ 6 * n + 1 := by omega
          simp [o] at l
          rw [l]
          rw [show 2 * (6 * n + 1) + 1 = 12 * n + 3 by ring]
          simp [s2]
        have s4: 3 * n ∈ s := by
          specialize l (3 * n)
          have o: 1 ≤ 3 * n := by omega
          simp [o] at l
          rw [l]
          rw [show 2 * (3 * n) = 6 * n by ring]
          simp [s3]
        simp [s4] at h
        simp [h]
    -- then we can prove the lemma
    constructor
    . intro f
      by_cases dm: Odd m
      . have eq: (m / 2) * 2 + 1 = m := by
          apply Nat.div_two_mul_two_add_one_of_odd dm
        specialize l (m / 2)
        clear r
        have o: 1 ≤ m / 2 := by omega
        simp [o] at l
        rw [l]
        rw [show 2 * (m / 2) = (m / 2) * 2 by ring]
        rw [eq]
        exact f
      . simp at dm
        have eq: (m / 2) * 2 = m := by
          apply Nat.div_two_mul_two_of_even dm
        specialize r (m / 2)
        clear l
        have o: 1 ≤ m / 2 := by omega
        simp [o] at r
        rw [r]
        rw [show 2 * (m / 2) = (m / 2) * 2 by ring]
        rw [eq]
        exact f
    . intro f
      by_cases dm: Odd m
      . have eq: (m / 2) * 2 + 1 = m := by
          apply Nat.div_two_mul_two_add_one_of_odd dm
        specialize l (m / 2)
        clear r
        have o: 1 ≤ m / 2 := by omega
        simp [o] at l
        rw [show 2 * (m / 2) = (m / 2) * 2 by ring] at l
        rw [eq] at l
        rw [← l]
        exact f
      . simp at dm
        have eq: (m / 2) * 2 = m := by
          apply Nat.div_two_mul_two_of_even dm
        specialize r (m / 2)
        clear l
        have o: 1 ≤ m / 2 := by omega
        simp [o] at r
        rw [show 2 * (m / 2) = (m / 2) * 2 by ring] at r
        rw [eq] at r
        rw [← r]
        exact f

  -- we use g to show that 1 ∈ s, but first we show that if the iterated division by two of m is in $s$ and is greater than $1$ then $m$ is $s$
  have key (m k : ℕ) (hm : 1 < (fun n => n / 2)^[k] m) : m ∈ s ↔ ((fun n => n / 2)^[k] m ∈ s) := by
    induction k
    case zero => simp
    case succ k ih =>
      have : 1 < (fun n => n / 2)^[k] m := 
        calc
        1 < (fun n => n / 2)^[k + 1] m := hm
        _ = (fun n => n / 2)^[k] m / 2  := by rw [Function.iterate_succ', Function.comp_apply]
        _ ≤ (fun n => n / 2)^[k] m := by omega
      rw [Function.iterate_succ', Function.comp_apply, ih, g _ this]
      exact this
  have : (fun n => n / 2)^[9] 2021 = 3 := by decide
  have h11 := g 3
  simp at h11

  specialize key 2021 9 (by simp)
  rw [key, this, h11] at h1
  clear * - h g h1
  -- then we can show that ∀ 1 ≤ n, n ∈ s by induction
  have f: ∀ n: ℕ, 1 ≤ n → n ∈ s := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    by_cases hn: n = 0
    . simp [hn]
    . replace hn: 1 ≤ n := by omega
      have gn:= g n
      by_cases ln: n = 1
      . simp [ln]
        exact h1
      . simp [hn]
        replace hn: 1 < n := by omega
        simp [hn] at gn
        apply gn.mpr
        have l: n / 2 < n := by omega
        specialize ih (n / 2)
        simp [l] at ih
        apply ih
        omega
  specialize f a
  apply f
  omega