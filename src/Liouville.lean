import ring_theory.algebraic
import topology.algebra.polynomial
import analysis.calculus.mean_value
import ring_theory.integral_closure
import data.polynomial.field_division
import field_theory.minimal_polynomial
import data.real.irrational
-- import small_things


noncomputable theory
open_locale classical

notation α`[X]` := polynomial α
notation `transcendental` x := ¬(is_algebraic ℤ x)


theorem liouville (α : ℝ) (ha : is_integral ℤ α) (hb : irrational α) : ∃ c : ℝ, c > 0 ∧ ∀ p q : ℤ, q > 0 → abs(α - p / q) > (c / q^(minimal_polynomial ha).nat_degree) :=
begin
sorry,
end