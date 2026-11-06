import Mathlib

theorem algebra_14173  :
  {n | ∃ p, Nat.Prime p ∧ n^2 - 35 * n + 306 = (p : ℤ)} = {16, 19} ∧ ({16, 19} :Finset ℤ).prod id = 304 := by 
  constructor
  · ext x
    simp 
    -- First we note that since $n^2-35n = n(n-35)$, and at least one of $n$ and $n-35$ is even, thus $n^2-35n$ is even. So $n^2-35n+306$ is also even.
    have : Even (x ^ 2 - 35 * x + 306) := by 
      have : Even (x^2 - 35 * x) := by 
        rw [show x^2 - 35 * x= x * (x - 35) by  ring_nf]
        rw [Int.even_mul]
        rcases Int.even_or_odd x  with evenx | oddx
        · tauto
        · exact Or.inr <| Int.even_sub'.2 (by simp [oddx]; decide)
      apply Int.even_add.2 
      simp [this] 
      decide 
    -- Thus the prime $p$ must equal 2. This means that we want the product of the positive integral solutions to $n^2-35n+306=2$, or $n^2-35n+304=0$.
    constructor <;> intro h 
    · obtain ⟨p, pp, hp⟩ := h
      have := (Nat.Prime.even_iff pp).1 (by convert hp ▸ this; simp) 
      simp [this] at hp 
      have : (x - 16) * (x - 19) = 0 := by nlinarith 
      simp at this ⊢
      omega 
    · -- Now prove the reverse. If x ∈ {16, 19}, then n^2 -35n +306 is prime
      rcases h with (rfl | rfl)
      · -- x =16
        use 2
        all_goals norm_num 
      · --x =19 
        use 2 
        all_goals norm_num 
  · -- Show the product is 304
    native_decide