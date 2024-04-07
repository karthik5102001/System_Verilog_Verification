// Code your design here
module FIFO( clock,reset,wr,rd,din,dout,full,empty);
  input  clock,reset,wr,rd;
  input  [7:0] din;
  output reg [7:0] dout;
  output  full,empty;
  
  parameter depth = 16;
  parameter size = 8;
  
  reg [3:0] wrptr = 0,rdptr = 0;
  reg [4:0] count = 0;
  reg [(size - 1) :0] memory_1 [(depth - 1) : 0];
  
  
  always @(posedge clock)
    begin
      
      if(reset)
        fork
          wrptr = 0;
          rdptr = 0;
          count = 0;
        join   
      
      else if (wr && ~full)
        begin 
          memory_1[wrptr] <= din;
          $display("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^");
          $display("[WRITE FROM DESIGN]: VALUE %0d",din); 
          $display("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^");
          wrptr <= wrptr+1;
          count <= count + 1;
        end
      
      else if (rd && !empty)
        begin
          dout <= memory_1[rdptr];
          $display("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^");
          $display("[READ FROM DESIGN]: VALUE %0d",dout);
          $display("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^");
          rdptr <= rdptr+1;
          count <= count - 1;
        end
      
    end
    
  assign empty = (count == 0) ? 1'b1  : 1'b0  ;
  assign full = ( count == (depth-1)) ? 1'b1 : 1'b0 ;


  
//////////////////////////////////////////ASSERTION//////////////////////////////////////////


  property reset_1;                                                 
    @(posedge clock) reset |=> ( !wrptr & !rdptr & !count );                   
  endproperty
  RESET : assert property (reset_1); //  $display("RESET SUCESS"); else $display("RESET FAIL");
  
  
  property full_checker;
    @(posedge clock) disable iff(reset) (wr && !full) && (count == (depth - 1)) |=> (full); 
  endproperty
    FULL : assert property (full_checker); // $display("FULL SUCESS"); else $display("FULL FAIL");
  
  property empty_checker;
    @(posedge clock) disable iff(reset) (rd && !empty) && (count == 0) |=> (empty); 
  endproperty
      EMPTY : assert property (empty_checker); // $display("EMPTY SUCESS"); else $display("EMPTY FAIL");
      
      
endmodule
      
      