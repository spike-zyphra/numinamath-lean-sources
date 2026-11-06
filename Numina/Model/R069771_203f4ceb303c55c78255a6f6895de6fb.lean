import Mathlib

theorem algebra_155503 (xiao_ming xiao_mei father : ℝ)
    (h : xiao_ming > 0) (h' : xiao_mei > 0) (h'' : father > 0)
    (h''' : father = 3 * xiao_ming) (h'''' : father = 2 * xiao_mei)
    (h''''' : xiao_ming * 6 = xiao_mei * 2) :
    father * 16 ≥ xiao_ming * 6 + xiao_mei * 2 := by
  nlinarith