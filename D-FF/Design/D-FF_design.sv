// Code your design here

module dff (D_IF.M2I  d_if);
 
  always @(posedge d_if.clock)
    begin
      
      if (d_if.reset == 1'b1)
        
        d_if.dout <= 1'b0;
      else
        d_if.dout <= d_if.din;
    end
endmodule
