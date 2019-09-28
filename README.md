# TLA-Specs

My personal TLA+ specifications.

* [Turnstile](#turnstile)
* [Soda Machine](#soda-machine)
* [Queue Processor](#queue-processor)


## Turnstile
<img src="http://yuml.me/diagram/scruffy/class/[note: Turnstile {bg:cornsilk}], [CoinFromLocked]->[CoinFromUnLocked], [CoinFromLocked]->[PushFromUnLocked], [CoinFromUnlocked]->[CoinFromUnlocked], [CoinFromUnlocked]->[PushFromUnlocked], [PushFromUnlocked]->[CoinFromLocked], [PushFromUnlocked]->[PushFromLocked], [PushFromLocked]->[PushFromLocked], [PushFromLocked]->[CoinFromLocked]"/>

## Soda Machine
<img src="http://yuml.me/diagram/scruffy/class/[note: Soda Machine {bg:cornsilk}], [AddMoney]->[AddMoney], [AddMoney]->[Dispense], [Dispense]->[AddMoney], [Dispense]->[ReturnChange], [ReturnChange]->[AddMoney]"/>


## Queue Processor
<img src="http://yuml.me/diagram/scruffy/class/[note: Queue Processing System {bg:cornsilk}], [SQS Queue]->[Queue Processor 2], [SQS Queue]->[Queue Processor 1], [Queue Processor 2]get_message->[SQS Queue], [Queue Processor 1]return_message->[SQS Queue], [Task Schedulr 3]->[SQS Queue], [Task Schedulr 2]->[SQS Queue], [Task Schedulr 1]->[SQS Queue]"/>
