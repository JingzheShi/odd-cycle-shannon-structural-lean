import C7Improvement.GraphRealisations

namespace ShannonBounds.C7Improvement

open scoped BigOperators

def M280 : ℕ :=
  454402134191994507126819903596564906706672995987342041247384728314329074657273274845475279319219681718758139567086979352344706380862194486578561

def M300 : ℕ :=
  8292850287950683069961562691270514917925807948370821800524044576544056421512701684580823442810854335415029684907044725214369985043992527534955657521950273

def baseline500Size : ℕ :=
  33964672918117456943408517573718333225317390754651100605971152590324909277046876400440353958428359262989621520394737276681196655776758386330470832773308559159990317076102131413374061066595834823529274560988950698158729501949866486079791784996498585401881281

theorem simple_layered_size : (∑ word ∈ K2.C, ∏ index : Fin 2, simpleRuleWeights (word index)) = M280 := by
  native_decide

theorem strong_layered_size : (∑ word ∈ K2.C, ∏ index : Fin 2, strongRuleWeights (word index)) = M300 := by
  native_decide

theorem simple_exponent : (∑ _ : Fin 2, ∑ index : Fin 3, simpleDimensions index) = 280 := by decide
theorem strong_exponent : (∑ _ : Fin 2, ∑ index : Fin 3, strongDimensions index) = 300 := by decide

theorem simple_strict_decimal_check : 3258834362237710 ^ 280 < M280 * (10 ^ 15) ^ 280 := by native_decide
theorem strong_strict_decimal_check : 3258834805519757 ^ 300 < M300 * (10 ^ 15) ^ 300 := by native_decide

theorem simple_beats_baseline_check : baseline500Size ^ 280 < M280 ^ 500 := by native_decide
theorem strong_beats_simple_check : M280 ^ 300 < M300 ^ 280 := by native_decide
theorem baseline_below_strong_decimal_check :
    baseline500Size * (10 ^ 15) ^ 500 < 3258834805519757 ^ 500 := by native_decide

end ShannonBounds.C7Improvement
