
module dff (dff_if.master  d_if);
 
  always @(posedge d_if.clk)
    begin
      
      if (d_if.rst == 1'b1)
        
        d_if.dout <= 1'b0;
      else
        d_if.dout <= d_if.din;
    end
endmodule
 
// Define an interface "dff_if" with the following signals
interface dff_if;
  logic clk;   // Clock signal
  logic rst;   // Reset signal
  logic din;   // Data input
  logic dout;  // Data output
  
  clocking cb @(posedge clk);
  default input #1 output #1;
    output din;
    input dout;
    endclocking

    modport master (input clk, rst, din, output dout);

endinterface