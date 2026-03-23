%==============================================================================
%  T Y P E   D E C L A R A T I O N S
%==============================================================================
 
type Four_Plex = array[ integer ];      % The four 12-bit integers that when
                                        % used together simulate a 48-bit
                                        % integer or the mantissa of a 64-bit
                                        % floating point number.
 
type Seed_Array = array[ Four_Plex ];   % One seed per process.
 
type Bit_Array = array[ integer ];      % The binary expansion of a Four_Plex.
 

