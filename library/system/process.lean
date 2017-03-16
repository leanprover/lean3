import .io

namespace process
-- Is there a way to remove meta constants from here?
meta constant builder : Type

meta constant builder.new (cmd : string) : io builder
meta constant builder.run : builder → io unit
meta constant builder.arg : builder → string → io unit

end process
