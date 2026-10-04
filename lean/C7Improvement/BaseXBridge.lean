import ShannonBounds.BaseC7

namespace ShannonBounds.C7Improvement

set_option maxRecDepth 100000

theorem baseX_list_eq : BaseC7.Xlist.toFinset = BaseC7.base.X := by
  ext point
  change point ∈ BaseC7.Xlist.toFinset ↔ point ∈ BaseC7.Xset
  simp only [List.mem_toFinset, BaseC7.mem_Xset]

end ShannonBounds.C7Improvement
