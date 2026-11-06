import Mathlib
open Real
/- 8. Dato il sistema

$$
\left\{\begin{array}{l}
x+y+z=7 \\
x^{2}+y^{2}+z^{2}=27 \\
x y z=5
\end{array}\right.
$$

quante terne ordinate di numeri reali $(x, y, z)$ ne sono soluzione?
(A) 6
(B) 3
(C) 2
(D) 0
(E) Infinite. -/
theorem algebra_135377 : {(x, y, z) : ℝ × ℝ × ℝ | x + y + z = 7 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 27 ∧ x * y * z = 5}.ncard = 3:= by
  -- We prove that the solution set equals exactly {(1, 1, 5), (1, 5, 1), (5, 1, 1)}
  have h1 : {(x, y, z) : ℝ × ℝ × ℝ | x + y + z = 7 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 27 ∧ x * y * z = 5} = {(1, 1, 5), (1, 5, 1), (5, 1, 1)}:= by
    -- Using extensionality to show set equality by proving both inclusions
    ext ⟨x, y, z⟩
    constructor
    -- Forward direction: if (x,y,z) satisfies the system, then it equals one of the three points
    .
      intro h
      simp at h
      rcases h with ⟨h1, h2, h3⟩
      -- Derive that x*y + y*z + z*x = 11 using the identity (x+y+z)^2 = x^2+y^2+z^2+2(xy+yz+zx)
      replace h2 : x * y + y * z + z * x = 11:= by
        replace h1 : (x + y + z) ^ 2 = 7 ^ 2:= by rw [h1]
        linarith
      -- Key insight: prove that (1-x)(1-y)(1-z) = 0 and (5-x)(5-y)(5-z) = 0
      -- This means at least one variable equals 1 and at least one equals 5
      have h4 : (1 - x) * (1 - y) * (1 - z) = 0:= by linarith
      have h5 : (5 - x) * (5 - y) * (5 - z) = 0:= by linarith
      simp at h4 h5
      -- Case analysis: one of x, y, or z equals 1
      rcases h4 with ⟨h4 | h4⟩ | h4
      -- Case: x = 1
      .
        replace h4 : x = 1:= by linarith
        subst x
        norm_num at h5
        rcases h5 with h5 | h5
        -- Subcase: y = 5, which forces z = 1
        .
          replace h5 : y = 5:= by linarith
          replace h1 : z = 1:= by linarith
          subst y z
          simp
        -- Subcase: z = 5, which forces y = 1
        .
          replace h5 : z = 5:= by linarith
          replace h1 : y = 1:= by linarith
          subst y z
          simp
      -- Case: y = 1
      .
        replace h4 : y = 1:= by linarith
        subst y
        norm_num at h5
        rcases h5 with h5 | h5
        -- Subcase: x = 5, which forces z = 1
        .
          replace h5 : x = 5:= by linarith
          replace h1 : z = 1:= by linarith
          subst x z
          simp
        -- Subcase: z = 5, which forces x = 1
        .
          replace h5 : z = 5:= by linarith
          replace h1 : x = 1:= by linarith
          subst x z
          simp
      -- Case: z = 1
      .
        replace h4 : z = 1:= by linarith
        subst z
        norm_num at h5
        rcases h5 with h5 | h5
        -- Subcase: x = 5, which forces y = 1
        .
          replace h5 : x = 5:= by linarith
          replace h1 : y = 1:= by linarith
          subst x y
          simp
        -- Subcase: y = 5, which forces x = 1
        .
          replace h5 : y = 5:= by linarith
          replace h1 : x = 1:= by linarith
          subst x y
          simp
    -- Backward direction: verify that each of the three points satisfies the system
    .
      intro h
      simp at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      all_goals
        simp
        norm_num
  -- Use the equality to compute the cardinality
  rw [h1]
  -- Convert the set to a finset to use card operations
  rw [show ({(1, 1, 5), (1, 5, 1), (5, 1, 1)} : Set (ℝ × ℝ × ℝ)) = ({(1, 1, 5), (1, 5, 1), (5, 1, 1)} : Finset (ℝ × ℝ × ℝ)) by simp]
  rw [Set.ncard_coe_Finset]
  -- Count the elements one by one, verifying they are distinct
  repeat rw [Finset.card_insert_of_not_mem]
  simp
  all_goals
    norm_num
