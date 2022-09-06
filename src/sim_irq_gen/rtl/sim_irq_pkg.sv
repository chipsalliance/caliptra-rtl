
package sim_irq_pkg;

typedef struct packed {
    logic [254:0] active_high;  // 1: actHi, 0: actLo
    logic [254:0] level_assert; // 1: level, 0: pulse
} irq_type_t;

endpackage
