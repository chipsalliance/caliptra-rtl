// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Created on 21.06.2023 at 10:50
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
// BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
// ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

module fv_constraints_m(init_cmd, next_cmd, reset_n, clk);
    input bit init_cmd, next_cmd, reset_n, clk;
    reg init_reg;
default clocking default_clk @(posedge clk); endclocking

    remove_init_next_together_a: assume property (remove_init_next_together);
    property remove_init_next_together;
        !(init_cmd && next_cmd);
    endproperty

    init_next_order_a: assume property (init_next_order);
    property init_next_order;
        !init_reg |-> !next_cmd;
    endproperty

    always @ (posedge clk or negedge reset_n)
        begin : init_reg_order
            if (!reset_n)
                init_reg <= 1'b0;
            else if (init_cmd)
                init_reg <= 1'b1;
        end

endmodule

bind sha512_core fv_constraints_m fv_constraints(
  .init_cmd(init_cmd),
  .next_cmd(next_cmd),
  .reset_n(reset_n),
  .clk(clk)
);