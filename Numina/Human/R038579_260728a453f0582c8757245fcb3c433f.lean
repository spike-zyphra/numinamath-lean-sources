import Mathlib
open Function

/- Let  $\mathbb{Z}$  be the set of all integers. Find all pairs of integers  $(a,b)$  for which there exist functions  $f \colon \mathbb{Z}\rightarrow \mathbb{Z}$  and  $g \colon \mathbb{Z} \rightarrow \mathbb{Z}$  satisfying
\[ f(g(x))=x+a \quad\text{and}\quad g(f(x))=x+b \]
for all integers  $x$ . -/
theorem algebra_605213 : { (a, b) : ℤ × ℤ | ∃ f g : ℤ → ℤ, ∀ x, f (g x) = x + a ∧ g (f x) = x + b } = { (a, b) | |a| = |b| } := by
  -- Main lemma:
  -- If a and b are integers such that there exist functions f and g from ℤ to ℤ satisfying f(g(x)) = x + a and g(f(x)) = x + b for all x, then |b| ≤ |a|.
  -- The main idea is to construct a function F from Fin b to Fin a, which is injective.
  have lm (a b : ℤ) : (∃ f g : ℤ → ℤ, ∀ x, f (g x) = x + a ∧ g (f x) = x + b) → b.natAbs <= a.natAbs := by
    intro ⟨f, g, h⟩

    -- f is injective because f(x) = f(y) implies g(f(x)) = g(f(y)), which implies x = y.
    have h1 : Injective f := by
      intro x y hxy
      apply_fun g at hxy
      simp only [h x, h y] at hxy
      linarith

    -- f(x + b) = f(x) + a by calculation.
    have h2 (x : ℤ) : f (x + b) = f x + a := by
      calc
        f (x + b) = f (g (f x)) := by rw [(h x).2]
                _ = f x + a := by rw [(h _).1]

    -- Rule out the case where a = 0.
    have h3 : a.natAbs = 0 ∨ a.natAbs > 0 := Nat.eq_zero_or_pos _
    cases h3 with
    | inl h3 =>
      replace h3 : a = 0 := Int.natAbs_eq_zero.1 h3
      have h4 : b = 0 := by
        apply_fun f
        rw [(by simp : b = 0 + b), h2 0, h3]
        simp
      rw [h3, h4]
    | inr h3 =>

      -- Main part here!
      -- First prove a lemma:
      -- f(x + k * b) = f(x) + k * a for all x and k.
      -- This is proved by induction on k.
      have hf (x k : ℤ) : f (x + k * b) = f x + k * a := by
        refine Int.inductionOn' k 0 ?_ ?_ ?_
        . simp
        . intro k _ hk
          calc
            f (x + (k + 1) * b) = f (x + k * b + b) := by ring_nf
                              _ = f x + k * a + a := by rw [h2, hk]
                              _ = f x + (k + 1) * a := by ring
        . intro k _ hk
          calc f (x + (k - 1) * b) = f (x + (k - 1) * b + b) - a := by rw [h2]; linarith
                                _ = f (x + k * b) - a := by ring_nf
                                _ = f x + (k - 1) * a := by rw [hk]; linarith

      -- Lemma to help construct the function F.
      -- x % |a| < |a| for all x.
      have Flem (x : ℤ) : (Int.fmod x a.natAbs).toNat < a.natAbs := by
        have h : Int.fmod x a.natAbs < a.natAbs := Int.fmod_lt_of_pos _ (Int.ofNat_pos.2 h3)
        refine (Int.toNat_lt' ?_).2 h
        exact Nat.not_eq_zero_of_lt h3

      -- Construct the function F.
      -- F(x) := x % |a| for all x = 0, 1, ..., |b| - 1.
      -- Thus F is a function from Fin b to Fin a.
      let F (x : Fin b.natAbs) : Fin a.natAbs := ⟨ (Int.fmod (f x) a.natAbs).toNat, Flem _ ⟩

      -- We now prove that F is injective.
      -- Assume F(x) = F(y), then f(x) % |a| = f(y) % |a|.
      -- This implies f(x) = f(y) + k * a for some k.
      -- Then x = y + k * b.
      -- This implies |b| divides x - y, which implies x = y.
      have Finj : Injective F := by
        intro x y hxy
        -- Simplify hxy to (f x).fmod |a| = (f y).fmod |a|.
        simp [F] at hxy
        apply_fun λ x => (x : ℤ) at hxy
        have h0 (x : ℤ) : (f x).fmod |a| ≥ 0 := Int.fmod_nonneg' _ (by linarith)
        rw [Int.toNat_of_nonneg (h0 x), Int.toNat_of_nonneg (h0 y)] at hxy

        let s := ((f x).fdiv |a| - (f y).fdiv |a|) * a.sign
        -- Prove by calculation that f(x) = f(y) + s * a.
        have h4 : f x = f y + s * a := by
          have h5 := Int.fmod_add_fdiv (f x) |a|
          have h6 := Int.fmod_add_fdiv (f y) |a|
          simp [s]
          have sign_mul_self' (a : ℤ) : a.sign * a = |a| := by rw [Int.sign_eq_sign a, sign_mul_self]
          rw [mul_assoc, sign_mul_self' a]
          ring_nf
          calc
            f x = (f x).fmod |a| + |a| * (f x).fdiv |a| := by symm; exact h5
              _ = (f y).fmod |a| + |a| * (f y).fdiv |a| + ((f x).fdiv |a| * |a| - (f y).fdiv |a| * |a|) := by rw [hxy]; ring
              _ = f y + ((f x).fdiv |a| * |a| - (f y).fdiv |a| * |a|) := by rw [h6]

        -- Prove that |b| divides x - y.
        rw [← hf] at h4
        replace h4 := h1 h4
        have h5 : b ∣ x - y := by rw [h4]; simp
        replace h5 : |b| ∣ x - y := (abs_dvd b _).2 h5

        -- Prove that x = y.
        have h6 : |↑↑x - ↑↑y| < (b.natAbs : ℤ) := by rw [abs_lt]; omega
        have h7 : x - y = (0 : ℤ) := by
          apply Int.eq_zero_of_abs_lt_dvd h5
          simp at h6
          exact h6
        replace h7 : (x : ℤ) = y := by linarith
        replace h7 : (x : ℕ) = y := Int.ofNat_inj.1 h7
        exact Fin.eq_of_val_eq h7

      -- F is injective, so |b| ≤ |a|.
      have h4 : Fintype.card (Fin b.natAbs) ≤ Fintype.card (Fin a.natAbs) := Fintype.card_le_of_injective F Finj
      simp at h4
      linarith


  -- Break the iff into two implications.
  ext ⟨a, b⟩
  simp
  constructor
  swap

  -- We prove that if |a| = |b|, then there exist f and g satisfying the conditions.
  . intro h
    simp [abs_eq_abs] at h
    -- Two cases: a = b and a = -b.
    cases h with
    | inl h =>
        rw [h]
        -- Set f(x) = x + 2b and g(x) = x + b.
        use (λx => x + 2 * b), (λx => x - b)
        intro x
        ring_nf
        tauto

    | inr h =>
        rw [h]
        -- Set f(x) = -x - 2b and g(x) = -x - b.
        use (λx => -x - 2 * b), (λx => -x - b)
        intro x
        ring_nf
        tauto

  -- We prove that if there exist f and g satisfying the conditions, then |a| = |b|.
  . intro ⟨f, g, h⟩
    -- |b| ≤ |a| by the main lemma.
    have h1 : b.natAbs ≤ a.natAbs := lm a b ⟨f, g, h⟩
    -- |a| ≤ |b| by symmetry.
    have h2 : a.natAbs ≤ b.natAbs := lm b a ⟨g, f, λx => ⟨(h x).2, (h x).1⟩⟩
    -- Combine the two inequalities.
    linarith
