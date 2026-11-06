import Mathlib
/-- Let $(G, \cdot)$ be a group that has no elements of order 4 and
    $f: G \rightarrow G$ be a group homomorphism that has the property
    $f(x) \in \{x, x^{-1}\}$ for all $x \in G$.
    Show that $f(x) = x$ for all $x \in G$, or $f(x) = x^{-1}$ for all $x \in G$. -/
theorem algebra_109618 {G : Type*} [Group G] (hG : ¬∃ x : G, orderOf x = 4)
    (f : G →* G) (hf : ∀ x : G, f x = x ∨ f x = x⁻¹) :
    (∀ x : G, f x = x) ∨ (∀ x : G, f x = x⁻¹) := by
  -- Suppose, for the sake of contradiction, that there exist $a,b \in G$
  by_contra h
  push_neg at h
  obtain ⟨⟨b,neb⟩, ⟨a,nea⟩⟩ := h
  -- such that $f(a) = a \neq a^{-1}$
  have eqa : f a = a := by specialize hf a; tauto
  -- and $f(b) = b^{-1} \neq b$.
  have eqb : f b = b ⁻¹ := by specialize hf b; tauto
  -- Then $f(ab) = f(a) f(b) = ab^{-1}
  have fab : f (a * b) = a * b ⁻¹ := by rw[map_mul, eqa, eqb]
  -- $\ne ab$ (since otherwise $b = b^{-1}$),
  have : f (a * b) ≠ a * b := by
    rw[fab]
    intro h
    have := mul_left_cancel h
    rw[← eqb] at this
    exact neb this
  -- so $f(ab) = (ab)^{-1} = b^{-1} a^{-1}$.
  have fab' : f (a * b) = (a * b) ⁻¹ := by specialize hf (a * b); tauto
  rw[fab] at fab'
  rw[mul_inv_rev] at fab'
  -- It follows that $ab^{-1} = b^{-1} a^{-1}, b^{-1} = ab^{-1}a$.
  have binv : b⁻¹ = a * b⁻¹ * a := by rw[fab']; group
  -- Then $f(ab^2) = f(a) f(b)^2 = ab^{-2}$.
  have fab2 : f (a * b^2) = a * (b ⁻¹)^2 := by rw[map_mul, map_pow, eqa, eqb]
  -- If $f(ab^2) = ab^2$,
  have : f (a * b^2) ≠ a * b^2 := by
    intro h
    rw[fab2] at h
    -- then $ab^{-2} = ab^2$,
    have := mul_left_cancel h
    -- $b^4 = e$, from which $ord(b) | 4$, so either
    have : b ^ 4 = 1 := by rwa[inv_pow, Eq.comm, eq_inv_iff_mul_eq_one, ← sq, ← pow_mul] at this
    have : orderOf b ∣ 2^2 := orderOf_dvd_of_pow_eq_one this
    have ⟨k,le,fact⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
    interval_cases k
    -- $b = e$, but then $f(b) = b$, or
    · simp only [pow_zero, orderOf_eq_one_iff] at fact
      rw[fact] at neb
      have : f 1 = 1 := by simp
      contradiction
    -- $b^2 = e$, a contradiction wth $b = b^{-1}$, or
    · have := inv_eq_self_of_orderOf_eq_two fact
      rw[this] at eqb
      contradiction
    -- $ord(b) = 4$, in contradiction to the hypothesis.
    · apply hG ⟨b, fact⟩
  -- Thus $f(ab^2) = (ab^2)^{-1} = b^{-2} a^{-1}$,
  have : f (a * b^2) = (a * b^2) ⁻¹ := by specialize hf (a * b^2); tauto
  rw[fab2, mul_inv_rev, ← inv_pow] at this
  -- so $ab^{-2}a = b^{-2}$.
  have : a * b ⁻¹ ^ 2 * a = b ⁻¹ ^ 2 := by rw[this]; group
  -- It follows that $ab^{-2}a = b^{-2} = ab^{-1}aab^{-1}a$,
  conv at this => rhs; rw[binv, sq]
  -- such that $b^{-2} = b^{-1} a a b^{-1}$, from which $a^2 = e$ -
  rw[← mul_assoc, ← mul_assoc, mul_right_cancel_iff,
     mul_assoc, mul_assoc, mul_assoc, mul_left_cancel_iff,
     sq, mul_left_cancel_iff, ← mul_assoc, Eq.comm, mul_left_eq_self, mul_eq_one_iff_eq_inv] at this
  -- a contradiction, as above.
  conv at eqa => rhs; rw[this]
  contradiction