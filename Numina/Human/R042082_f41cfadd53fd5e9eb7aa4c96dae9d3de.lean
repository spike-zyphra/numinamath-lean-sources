import Mathlib

/- 5. The devil of numbers has colored all integers: each number is now either black or white. The number 1 is white. For any pair of white numbers $a$ and $b$ (the numbers $a$ and $b$ can be the same), $a-b$ and $a+b$ have different colors.

Prove that the number 2011 is white. -/

theorem number_theory_172674 {f : ℤ → Fin 2} (h1 : f 1 = 1) (h2 : ∀ a b, f a = 1 → f b = 1 → f (a - b) ≠ f (a + b)) :
    f 2011 = 1 := by

    --Two basic facts based on the assumptions。 We need to prove the proposition for the next lemma.
    have f00 : f 0 = 0 := by
      by_contra f01
      have : f 0 = 1 := by omega
      have : f (1-0) ≠ f (1+0) := by apply h2; exact h1; exact this
      simp at this
    have f21 : f 2 = 1 := by
      have : f (1-1) ≠ f (1+1) := by apply h2; exact h1; exact h1
      simp at this
      omega

    -- Now we do the induction to prove that the colors should go like black white white...
    have lem : ∀ k : ℕ, f ((3*k)) = 0  ∧ f ((3*k)+1) = 1 ∧ f ((3*k)+2) = 1 := by
      intro k
      induction' k with k hk
      simp; tauto

      obtain ⟨h3k, h3kp1, h3kp2⟩ := hk 

      have s1: f (3 * ↑(k + 1)) = 0 := by
        have t1: f (3 * ↑k + 2 - 1) ≠ f (3 * ↑k + 2 + 1) := by 
          apply h2
          assumption 
          assumption
        simp at t1 ⊢;
        have : 3 * ((k:ℤ) + 1) = 3 * ↑k + 2 + 1 := by ring_nf
        rw [this]; 
        have : 3 * (k:ℤ) + 2 - 1 = 3 * (k:ℤ) + 1 := by ring_nf
        rw [this] at t1; 
        omega

      have s2: f (3 * ↑(k + 1) + 1) = 1 := by
        have t1 : f (3 * ↑k + 2 - 2) ≠ f (3 * ↑k + 2 + 2) := by 
          apply h2
          assumption 
          assumption
        simp at t1 ⊢;
        have : 3 * ((k:ℤ) + 1) + 1 = 3 * ↑k + 2 + 2 := by ring_nf
        rw [this]
        have : 3 * (k:ℤ) + 2 - 2 = 3 * ↑k := by omega
        omega

      have s3: f (3 * ↑(k + 1) + 2) = 1 := by
        have t1: f (3 * ↑(k + 1) + 1 - 1) ≠ f (3 * ↑(k + 1) + 1 + 1) := by
          apply h2
          assumption
          assumption
        have : 3 * (@Nat.cast ℤ instNatCastInt (k + 1) ) + 2 = 3 * ↑(k + 1) + 1 + 1 := by ring_nf
        rw [this]
        have : 3 * (@Nat.cast ℤ instNatCastInt (k + 1)) + 1 - 1 = 3 * (@Nat.cast ℤ instNatCastInt (k + 1)) := by ring_nf
        rw [this] at t1
        omega 

      tauto


    --Apply the previous claim and we get 2011 is white.
    have cla : f (3 * ↑670) = 0 ∧ f (3 * ↑670 + 1) = 1 ∧ f (3 * ↑670 + 2) = 1 := by apply lem 670
    have cla2: f (3 * ↑670 + 1) = 1 := by exact cla.right.left
    ring_nf at cla2; assumption