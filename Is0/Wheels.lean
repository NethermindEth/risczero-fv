namespace Risc0

namespace Wheels

namespace Option

@[simp]
theorem get_some {α : Type} [Inhabited α] {x : α} :
  @Option.get! α _ (some x) = x := rfl

end Option

end Wheels

end Risc0