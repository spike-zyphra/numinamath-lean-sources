import Mathlib

/-The numbers in the sequence 101, 104, 109,116,… are of the form a_n=100+n^2,where n=1,2,3,… For each n, let d_n be the greatest common divisor of a_n and a_{n+1}. Find the maximum value of d_n as n ranges through the positive integers.-/
def a (n : ℕ) := 100 + n ^ 2

def d (n : ℕ) := Nat.gcd (a n) (a (n + 1))

theorem number_theory_94755 : IsGreatest {d n | n > 0} 401 := by
--We prove the greatest number is 401 by prove that it can be achieved when n=200 and d n divides 401 for each n.
  simp only [IsGreatest]
  constructor
--First we prove 401 lies in the set.
  · simp only [gt_iff_lt, Set.mem_setOf_eq]
    use 200
    simp only [d,a]
    norm_num
--Now, we prove that 401 is an upper bound.
  · simp only [upperBounds,gt_iff_lt, Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,d,a]
    intro n hn
--The left hand side is the same as gcd (100+n^2,2*n+1)
    rw[←Nat.gcd_sub_self_right (by linarith)]
    have :100+(n+1)^2-(100+n^2)=2*n+1:=by
      rw[←(Int.natCast_inj),Nat.cast_add,Int.natCast_sub (by linarith)]
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one, add_sub_add_left_eq_sub,
      Nat.cast_mul]
      ring
    rw[this]
--We prove the left hand side divides 401.
    apply Nat.le_of_dvd (by norm_num)
--It suffices to prove that Nat.gcd (400+4* n^2) (2*n+1)∣ 401
    suffices Nat.gcd (400+4*n^2) (2*n+1)∣ 401 by
      apply dvd_trans _ this
      apply gcd_dvd_gcd
      use 4;ring;rfl
--We calculate Nat.gcd (400+4* n^2) (2*n+1)∣ 401
    have ex:400+4*n^2=(2*n+1)*(2*n-1)+401:=by
      rw[←Int.natCast_inj]
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
      rw[Int.natCast_sub (by linarith),Nat.cast_mul]
      ring
--Because gcd(a,b)∣ a, we got the desired property.
    rw[ex,add_comm,Nat.gcd_add_mul_left_left]
    apply gcd_dvd_left