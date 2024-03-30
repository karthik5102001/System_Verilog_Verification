
class transaction;
rand bit [4:0] din;
rand bit [4:0] dout;

function transaction copy();
  transaction t;
  t = new();
  t.din = this.din;
  t.dout = this.dout;
endfunction


function void print(input string str);
  $display(" %0s : din = %0d, dout = %0d", str, din, dout);
endfunction

endclass

////////////////////////////---GENERATOR---/////////////////////////////////////


class generator;

transaction trans;       /// Transaction object

event done;              /// Event to notify the end of the test
event wait_scrb;         /// Event to wait for the scorebaord

int count;              /// Number of transactions to be generated

mailbox #(transaction) gen2drv_mbox;           /// Mailbox to send transactions to driver
mailbox #(transaction) gen2score_mbox;         /// Mailbox to send transactions to scoreboard

function new(mailbox #(transaction) gen2drv_mbox, mailbox #(transaction) gen2score_mbox); /// Constructor
    this.gen2drv_mbox = gen2drv_mbox;
    this.gen2score_mbox = gen2score_mbox;
endfunction


task run();                      /// Task to generate transactions
    repeat(count)                /// Repeat for the number of transactions
    begin
      assert(trans.randomize) else $error("Randomization failed");  /// Randomize the transaction
      gen2drv_mbox.put(trans.copy);                                 /// Send the transaction to driver
      gen2score_mbox.put(trans.copy);                               /// Send the transaction to scoreboard
      $display("[GEN] : DUMPED TRANSACTION");                       
      trans.print("[GEN]");                                         /// Print the transaction
      @(wait_scrb);                                                  /// Wait for the scoreboard to process the transaction
    end
    -> done;                                                            /// Notify the end of the test
endtask
endclass


////////////////////////////---DRIVER---/////////////////////////////////////

class driver;
transaction trans;       /// Transaction object
mailbox #(transaction) gen2drv_mbox;           /// Mailbox to receive transactions from generator
virtual dff_if d_if;                          /// Virtual interface to connect to DUV

function new(mailbox #(transaction) gen2drv_mbox);
    this.gen2drv_mbox= gen2drv_mbox; // Initialize the mailbox for receiving data
  endfunction

task reset();
    d_if.rst <= 1'b1;                           /// Assert reset signal
    repeat(5) @(posedge d_if.clk);              //// Wait for 5 clock cycles
    d_if.rst <= 1'b0;                           /// Deassert reset signal
    @(posedge d_if.clk);                        /// Wait for one more clock cycle
    $display("[DRV] : RESET DONE");             //// Display reset completion message
  endtask
  
task run();
    forever begin
      gen2drv_mbox.get(trans);             /// Get a transaction from the generator
      d_if.din <= trans.din;                 /// Set DUT input from the transaction
      @(posedge d_if.clk);                 /// Wait for the rising edge of the clock
      trans.print("DRV");                   //// Display transaction information
      d_if.din <= 1'b0;                   /// Set DUT input to 0
      @(posedge d_if.clk);                /// Wait for the rising edge of the clock
    end
  endtask
  
endclass


////////////////////////////---MONITOR---/////////////////////////////////////